import VerifiedGarbage.Spec.Aes

/-!
# AES-GCM-SIV (RFC 8452)

**Trusted** (as every file in `Spec/`). The nonce-misuse-resistant AEAD
AES-GCM-SIV, transcribed from RFC 8452, *AES-GCM-SIV: Nonce Misuse-Resistant
Authenticated Encryption* (April 2019); section numbers below refer to it.
As the RFC defines it, every input is a string of whole bytes.

AES-GCM-SIV takes a key-generating key of 16 bytes (AEAD_AES_128_GCM_SIV)
or 32 bytes (AEAD_AES_256_GCM_SIV), and a 12-byte nonce (§6). For each
nonce it derives a message-authentication key and a message-encryption key
from the key-generating key (§4, `deriveKeys`), authenticates the additional
data and the plaintext with POLYVAL (§3), encrypts the result into the tag,
and encrypts the plaintext with AES in counter mode from the tag (§4,
`ctr`).

Everything but the key-generating key's cipher is computed per message, so
the functions take that cipher, `CIPH_K`, as a function on 16-byte blocks
(`Cipher`), with the key's length (`encryptWith`, `decryptWith`);
`encrypt` and `decrypt` are AES-GCM-SIV with a key, as the RFC defines
them (`encrypt_eq`, `decrypt_eq`). The contracts of the functions
implemented in assembly are in `Spec/GcmSiv/Contract.lean`.

The RFC's limits on the lengths (§4, §5, §6: at most 2³⁶ bytes of
plaintext and of additional data) are `supported`; the RFC's `encrypt` and
`decrypt` fail beyond them, which `encrypt` and `decrypt` here do.
-/

namespace VG.Spec.GcmSiv

/-- The forward function of AES under some key, on 16-byte blocks. -/
abbrev Cipher := List Byte → List Byte

/-! ## Encodings -/

/-- `little_endian_uint32(x)`: the 4 bytes of `x mod 2³²`, the least
significant first. -/
def le32 (x : Nat) : List Byte := (List.range 4).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

/-- `little_endian_uint64(x)`: the 8 bytes of `x mod 2⁶⁴`, the least
significant first. -/
def le64 (x : Nat) : List Byte := (List.range 8).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

/-- `read_little_endian_uint32`: the number whose little-endian bytes are
`bs`. -/
def leNat (bs : List Byte) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- `n` zero bytes. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- `right_pad_to_multiple_of_16_bytes` (§4): `bs` followed by the fewest
zero bytes that make its length a multiple of 16. -/
def pad16 (bs : List Byte) : List Byte := bs ++ zeros ((16 - bs.length % 16) % 16)

/-! ## POLYVAL (§3) -/

/-- An element of the field of 2¹²⁸ elements, as the `BitVec 128` whose bit
`i` is the coefficient of `xⁱ`. -/
abbrev Elem := BitVec 128

/-- §3: the field element of a 16-byte string, "taking the least
significant bit of the first byte to be the coefficient of x^0, the most
significant bit of the first byte to be the coefficient of x^7, and so on,
until the most significant bit of the last byte is the coefficient of
x^127": the 16 bytes as a little-endian number. -/
def ofBytes (bs : List Byte) : Elem := BitVec.ofNat 128 (leNat bs)

/-- The 16-byte string of a field element (the inverse of `ofBytes`). -/
def toBytes (x : Elem) : List Byte := (List.range 16).map fun i => x.extractLsb' (8 * i) 8

/-- The field elements of a string whose length is a multiple of 16: one per
16 bytes. -/
def elems (bs : List Byte) : List Elem :=
  (List.range (bs.length / 16)).map fun i => ofBytes ((bs.drop (16 * i)).take 16)

/-- §3: the irreducible polynomial `x¹²⁸ + x¹²⁷ + x¹²⁶ + x¹²¹ + 1`, less its
`x¹²⁸` term. -/
def poly : Elem := (1 <<< 127) ||| (1 <<< 126) ||| (1 <<< 121) ||| 1

/-- The product of `a` and `x`, reduced modulo the irreducible polynomial:
shift every coefficient up by one, and if the coefficient of `x¹²⁷` was 1,
replace the resulting `x¹²⁸` by `x¹²⁷ + x¹²⁶ + x¹²¹ + 1`. -/
def mulX (a : Elem) : Elem := if a.getLsbD 127 then (a <<< 1) ^^^ poly else a <<< 1

/-- §3: the product of two field elements, "standard (binary) polynomial
multiplication followed by reduction modulo the irreducible polynomial":
`Σ aᵢ · b · xⁱ`, by Horner's rule from the coefficient of `x¹²⁷` down. -/
def mul (a b : Elem) : Elem :=
  (List.range 128).foldl (fun z i => if a.getLsbD (127 - i) then mulX z ^^^ b else mulX z) 0

/-- §3: "the field element `x⁻¹²⁸` is equal to
`x¹²⁷ + x¹²⁴ + x¹²¹ + x¹¹⁴ + 1`". -/
def xInv128 : Elem := (1 <<< 127) ||| (1 <<< 124) ||| (1 <<< 121) ||| (1 <<< 114) ||| 1

/-- §3: `dot(a, b) = a * b * x⁻¹²⁸`. -/
def dot (a b : Elem) : Elem := mul (mul a b) xInv128

/-- §3, POLYVAL continued from `S` over the field elements `X`:
`Sⱼ = dot(Sⱼ₋₁ + Xⱼ, H)`. POLYVAL itself starts from `S₀ = 0`. -/
def polyvalFrom (h s : Elem) (xs : List Elem) : Elem := xs.foldl (fun s x => dot (s ^^^ x) h) s

/-- §3, `POLYVAL(H, X_1, …, X_s)`: `S_s`, where `S₀ = 0` and
`Sⱼ = dot(Sⱼ₋₁ + Xⱼ, H)`. -/
def polyval (h : Elem) (xs : List Elem) : Elem := polyvalFrom h 0 xs

/-! ## Encryption (§4) -/

/-- §4, `derive_keys(key_generating_key, nonce)` for a key-generating key of
`keyLen` bytes (16 or 32) whose cipher is `ciph`: the message-authentication
key, the first 8 bytes of `CIPH_K(little_endian_uint32(i) ‖ nonce)` for `i`
of 0 and 1, and the message-encryption key, the same for `i` from 2 to 3
(a 16-byte key-generating key) or to 5 (a 32-byte one). -/
def deriveKeys (ciph : Cipher) (keyLen : Nat) (nonce : List Byte) : List Byte × List Byte :=
  let half (i : Nat) := (ciph (le32 i ++ nonce)).take 8
  (half 0 ++ half 1, (List.range (keyLen / 8)).flatMap fun i => half (i + 2))

/-- §4, the block that is encrypted into the tag, for the
message-authentication key `authKey`: `S_s = POLYVAL(authKey, X_1, X_2, …)`
of the padded additional data, the padded plaintext and the length block
`little_endian_uint64(bytelen(additional_data) * 8) ‖
little_endian_uint64(bytelen(plaintext) * 8)`, with its first twelve bytes
XORed with the nonce and the most significant bit of its last byte
cleared. -/
def tagInput (authKey nonce pt aad : List Byte) : List Byte :=
  let lengthBlock := le64 (8 * aad.length) ++ le64 (8 * pt.length)
  let s := toBytes (polyval (ofBytes authKey) (elems (pad16 aad ++ pad16 pt ++ lengthBlock)))
  (List.range 16).map fun i =>
    if i < 12 then s.getD i 0 ^^^ nonce.getD i 0
    else if i = 15 then s.getD i 0 &&& 0x7f
    else s.getD i 0

/-- §4, the counter block `i` blocks after `icb`: its first 4 bytes, as a
little-endian number, incremented `i` times modulo 2³², and its other 12
bytes. -/
def counterBlock (icb : List Byte) (i : Nat) : List Byte :=
  le32 ((leNat (icb.take 4) + i) % 2 ^ 32) ++ icb.drop 4

/-- §4, `AES_CTR(key, initial_counter_block, in)` for the cipher `ciph` of
`key`: `in` XORed with the keystream `CIPH(CB₀) ‖ CIPH(CB₁) ‖ …`, where
`CBᵢ` is `counterBlock icb i`, truncated to the length of `in`. -/
def ctr (ciph : Cipher) (icb input : List Byte) : List Byte :=
  let ks := (List.range ((input.length + 15) / 16)).flatMap fun i => ciph (counterBlock icb i)
  List.zipWith (· ^^^ ·) input ks

/-- The initial counter block of a tag (§4): "the tag with the most
significant bit of the last byte set to one". -/
def initialCounter (tag : List Byte) : List Byte :=
  (List.range 16).map fun i => if i = 15 then tag.getD i 0 ||| 0x80 else tag.getD i 0

/-- The cipher of AES with `nr` rounds and the key schedule `w` (as bytes,
FIPS 197). -/
def aesWith (nr : Nat) (w : List Byte) : Cipher := fun x =>
  (Aes.cipher nr w (Vector.ofFn fun i => x.getD i 0)).toList

/-- The cipher of AES under a key of 16, 24 or 32 bytes (FIPS 197). -/
def aes (key : List Byte) : Cipher := aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)

/-- §4, `encrypt(key_generating_key, nonce, plaintext, additional_data)`
once the lengths are accepted, for a key-generating key of `keyLen` bytes
whose cipher is `ciph`: the encrypted plaintext and the 16-byte tag (whose
concatenation is the RFC's result).
```
message_authentication_key, message_encryption_key = derive_keys(K, nonce)
tag = AES(message_encryption_key, S_s)          (S_s as in `tagInput`)
ciphertext = AES_CTR(message_encryption_key, tag with bit 7 of byte 15 set, plaintext)
``` -/
def encryptWith (ciph : Cipher) (keyLen : Nat) (nonce pt aad : List Byte) :
    List Byte × List Byte :=
  let (authKey, encKey) := deriveKeys ciph keyLen nonce
  let tag := aes encKey (tagInput authKey nonce pt aad)
  (ctr (aes encKey) (initialCounter tag) pt, tag)

/-- §5, `decrypt(key_generating_key, nonce, ciphertext, additional_data)`
once the lengths are accepted, for a key-generating key of `keyLen` bytes
whose cipher is `ciph`, the encrypted plaintext `ct` and the tag `tag` (the
RFC's ciphertext is `ct ‖ tag`): the plaintext
`AES_CTR(message_encryption_key, tag with bit 7 of byte 15 set, ct)` if the
tag computed from it (as `encryptWith` computes it) is `tag`, and `none`
(fail) if not. -/
def decryptWith (ciph : Cipher) (keyLen : Nat) (nonce ct aad tag : List Byte) :
    Option (List Byte) :=
  let (authKey, encKey) := deriveKeys ciph keyLen nonce
  let pt := ctr (aes encKey) (initialCounter tag) ct
  if aes encKey (tagInput authKey nonce pt aad) = tag then some pt else none

/-- §4 and §5: the lengths (in bytes) of plaintext (at most 2³⁶) and
additional data (at most 2³⁶) for which encryption and decryption are
defined. -/
def supported (ptLen aadLen : Nat) : Bool := ptLen ≤ 2 ^ 36 && aadLen ≤ 2 ^ 36

/-- §4, AES-GCM-SIV encryption under the key-generating key `key` (16 or
32 bytes) of the plaintext `pt` with the additional data `aad` under the
12-byte `nonce`: the RFC's result, the encrypted plaintext followed by the
tag, or `none` (fail) if a length is too long. -/
def encrypt (key nonce pt aad : List Byte) : Option (List Byte) :=
  if supported pt.length aad.length then
    let (ct, tag) := encryptWith (aes key) key.length nonce pt aad
    some (ct ++ tag)
  else none

/-- §5, AES-GCM-SIV decryption under the key-generating key `key` (16 or
32 bytes) of the ciphertext `c` (the encrypted plaintext followed by the
16-byte tag) with the additional data `aad` under the 12-byte `nonce`:
`none` (fail) if `c` is shorter than 16 bytes or a length is too long, and
otherwise `decryptWith`'s result. -/
def decrypt (key nonce c aad : List Byte) : Option (List Byte) :=
  if c.length < 16 || !supported (c.length - 16) aad.length then none
  else decryptWith (aes key) key.length nonce (c.take (c.length - 16)) aad (c.drop (c.length - 16))

/-! ## On memory -/

/-- The cipher of AES with `nr` rounds and the key schedule in the first
`16 (nr + 1)` bytes at `p` (as `vg_aes_expand_key` writes it). -/
def ctxCiph (m : Mem) (p : Addr) (nr : Nat) : Cipher :=
  aesWith nr (Aes.bytesAt m p (16 * (nr + 1)))

/-- The length in bytes of an AES key for `nr` rounds (FIPS 197 §5,
`Nr = Nk + 6`). -/
def keyLen (nr : Nat) : Nat := 4 * (nr - 6)

/-- The key schedule of `key`, for its number of rounds, has the cipher of
AES with `key`. -/
theorem ctxCiph_eq {m : Mem} {p : Addr} {key : List Byte}
    (hk : Aes.bytesAt m p (16 * (Aes.rounds (key.length / 4) + 1)) = Aes.expandKey key) :
    ctxCiph m p (Aes.rounds (key.length / 4)) = aes key := by
  rw [ctxCiph, hk, aes]

/-- Encryption with the key schedule of `key` (for its number of rounds) is
AES-GCM-SIV encryption with `key`. -/
theorem encryptWith_ctx {m : Mem} {p : Addr} {key : List Byte}
    (hl : key.length = 16 ∨ key.length = 32)
    (hk : Aes.bytesAt m p (16 * (Aes.rounds (key.length / 4) + 1)) = Aes.expandKey key)
    (nonce pt aad : List Byte) (hs : supported pt.length aad.length = true) :
    encrypt key nonce pt aad =
      some ((encryptWith (ctxCiph m p (Aes.rounds (key.length / 4)))
          (keyLen (Aes.rounds (key.length / 4))) nonce pt aad).1 ++
        (encryptWith (ctxCiph m p (Aes.rounds (key.length / 4)))
          (keyLen (Aes.rounds (key.length / 4))) nonce pt aad).2) := by
  have hn : keyLen (Aes.rounds (key.length / 4)) = key.length := by
    unfold keyLen Aes.rounds; omega
  rw [ctxCiph_eq hk, hn, encrypt]
  simp only [hs, ↓reduceIte]

/-- Decryption with the key schedule of `key` (for its number of rounds) is
AES-GCM-SIV decryption with `key`, for lengths that are accepted. -/
theorem decryptWith_ctx {m : Mem} {p : Addr} {key : List Byte}
    (hl : key.length = 16 ∨ key.length = 32)
    (hk : Aes.bytesAt m p (16 * (Aes.rounds (key.length / 4) + 1)) = Aes.expandKey key)
    (nonce ct aad tag : List Byte) (ht : tag.length = 16)
    (hs : supported ct.length aad.length = true) :
    decrypt key nonce (ct ++ tag) aad =
      decryptWith (ctxCiph m p (Aes.rounds (key.length / 4)))
        (keyLen (Aes.rounds (key.length / 4))) nonce ct aad tag := by
  have hn : keyLen (Aes.rounds (key.length / 4)) = key.length := by
    unfold keyLen Aes.rounds; omega
  have hc : (ct ++ tag).length - 16 = ct.length := by simp [ht]
  have hlt : decide ((ct ++ tag).length < 16) = false := by simp [ht]
  rw [ctxCiph_eq hk, hn, decrypt, hc, hs, hlt]
  simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.take_left,
    List.drop_left]

end VG.Spec.GcmSiv

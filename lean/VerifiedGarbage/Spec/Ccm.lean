import VerifiedGarbage.Spec.Aes

/-!
# CCM (NIST SP 800-38C)

**Trusted** (as every file in `Spec/`). The Counter with Cipher Block
Chaining-Message Authentication Code mode of a 128-bit block cipher,
transcribed from NIST SP 800-38C, *Recommendation for Block Cipher Modes of
Operation: The CCM Mode for Authentication and Confidentiality* (May 2004,
errata update July 2007), with the formatting function and counter
generation function of its Appendix A, the ones every implementation we
test against uses (they are also RFC 3610's); section numbers below refer
to it. Appendix A.1 requires every string to be a string of whole bytes.

CCM is defined here for any block cipher, given as its forward function
`CIPH_K` on 16-byte blocks (`Cipher`); `aesCcmEncrypt` and `aesCcmDecrypt`
are CCM with AES. Its parameters are the length `t` of the MAC in bytes and
the length `n` of the nonce in bytes (A.1: `t ∈ {4, 6, …, 16}`,
`n ∈ {7, …, 13}`), which determines the length `q = 15 − n` of the payload's
length field; the payload is shorter than `2^(8q)` bytes. The contracts of
the functions implemented in assembly are in `Spec/Ccm/Contract.lean`.

The ciphertext of §6 is the encrypted payload followed by the encrypted MAC.
`encryptWith` and `decryptWith` take and return them apart: the encrypted
payload, which has the length of the payload, and the encrypted MAC of `t`
bytes, the tag.

§6.2 step 1 rejects a ciphertext of `Clen ≤ Tlen` bits, that is with an
empty payload, although Appendix A's formatting function accepts an empty
payload (`p = 0`), §6.1 encrypts it, and the CAVP's own decryption vectors
(`DVPT`, `Plen = 0`) expect it to be decrypted, as RFC 3610 does (§2.1:
`0 <= l(m)`).
`decrypt` follows the CAVP vectors: it rejects a ciphertext shorter than the
tag (`Clen < Tlen`), and accepts one with an empty payload.
-/

namespace VG.Spec.Ccm

/-- A block cipher's forward function `CIPH_K` on 16-byte blocks. -/
abbrev Cipher := List Byte → List Byte

/-- `n` zero bytes. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- `X ⊕ Y` on byte strings, as long as the shorter of the two. -/
def xor (x y : List Byte) : List Byte := List.zipWith (· ^^^ ·) x y

/-- `[x]₈ₖ`, the binary representation of `x` in `k` bytes (§5.5), the most
significant first (modulo `2^(8k)`). -/
def be (k x : Nat) : List Byte := (List.range k).map fun i => BitVec.ofNat 8 (x / 256 ^ (k - 1 - i))

/-- `bs` followed by the fewest zero bytes, possibly none, that make its
length a multiple of 16 (A.2.2, A.2.3). -/
def pad16 (bs : List Byte) : List Byte := bs ++ zeros ((16 - bs.length % 16) % 16)

/-- The 16-byte blocks of a string whose length is a multiple of 16. -/
def blocks (bs : List Byte) : List (List Byte) :=
  (List.range (bs.length / 16)).map fun i => (bs.drop (16 * i)).take 16

/-! ## Appendix A: formatting and counter generation -/

/-- A.1, the MAC lengths `t` (in bytes) the formatting allows:
`t ∈ {4, 6, 8, 10, 12, 14, 16}`. -/
def tagLenOk (t : Nat) : Bool := 4 ≤ t && t ≤ 16 && t % 2 == 0

/-- A.1, the nonce lengths `n` (in bytes) the formatting allows:
`n ∈ {7, 8, 9, 10, 11, 12, 13}`, for which `q = 15 − n ∈ {2, …, 8}`. -/
def nonceLenOk (n : Nat) : Bool := 7 ≤ n && n ≤ 13

/-- A.1, the length conditions of the formatting: the MAC length `t` and
the nonce length `n` are allowed, the payload is shorter than `2^(8q)`
bytes for `q = 15 − n` (`p < 2^(8q)`), and the associated data shorter than
2⁶⁴ bytes (`a < 2⁶⁴`). -/
def valid (t n a p : Nat) : Bool :=
  tagLenOk t && nonceLenOk n && p < 2 ^ (8 * (15 - n)) && a < 2 ^ 64

/-- A.2.1, Table 1, the flags octet of `B₀`: bit 7 `Reserved` (0), bit 6
`Adata` (1 if `a > 0`), bits 5–3 `[(t−2)/2]₃` and bits 2–0 `[q−1]₃`. -/
def flags (t q a : Nat) : Byte :=
  BitVec.ofNat 8 ((if a > 0 then 64 else 0) + 8 * ((t - 2) / 2) + (q - 1))

/-- A.2.1, Table 2, the first block `B₀`: the flags, the nonce `N` (octets
1 to `15 − q`) and `Q = [p]₈q` (octets `16 − q` to 15), for the MAC length
`t`, the nonce `nonce`, `a` bytes of associated data and `p` bytes of
payload. -/
def b0 (t : Nat) (nonce : List Byte) (a p : Nat) : List Byte :=
  let q := 15 - nonce.length
  flags t q a :: nonce ++ be q p

/-- A.2.2, the encoding of the length `a > 0` of the associated data:
`[a]₁₆` if `0 < a < 2¹⁶ − 2⁸`, `0xff ‖ 0xfe ‖ [a]₃₂` if
`2¹⁶ − 2⁸ ≤ a < 2³²`, and `0xff ‖ 0xff ‖ [a]₆₄` if `2³² ≤ a < 2⁶⁴`. -/
def encodeLen (a : Nat) : List Byte :=
  if a < 2 ^ 16 - 2 ^ 8 then be 2 a
  else if a < 2 ^ 32 then [0xff, 0xfe] ++ be 4 a
  else [0xff, 0xff] ++ be 8 a

/-- A.2, the formatting of `(N, A, P)` into the blocks `B₀, B₁, …, Bᵣ`
for the MAC length `t`: `B₀` (A.2.1); if `a > 0`, the encoding of `a`
followed by `A`, padded with zeros to whole blocks (A.2.2); and `P`, padded
with zeros to whole blocks (A.2.3). -/
def format (t : Nat) (nonce aad pt : List Byte) : List (List Byte) :=
  let adata := if aad.length = 0 then [] else pad16 (encodeLen aad.length ++ aad)
  blocks (b0 t nonce aad.length pt.length ++ adata ++ pad16 pt)

/-- A.3, Tables 3 and 4, the counter block `Ctrᵢ`: the flags `[q−1]₃` (the
other bits 0), the nonce `N` and `[i]₈q`. -/
def ctrBlock (nonce : List Byte) (i : Nat) : List Byte :=
  let q := 15 - nonce.length
  BitVec.ofNat 8 (q - 1) :: nonce ++ be q i

/-! ## The CCM processes (§6) -/

/-- §6.1 steps 1–4, the MAC `T = MSB_Tlen(Yᵣ)` of `t` bytes, where
`Y₀ = CIPH_K(B₀)` and `Yᵢ = CIPH_K(Bᵢ ⊕ Yᵢ₋₁)` for the blocks
`B₀, …, Bᵣ` of `format`. -/
def mac (ciph : Cipher) (t : Nat) (nonce aad pt : List Byte) : List Byte :=
  match format t nonce aad pt with
  | [] => []
  | b :: bs => (bs.foldl (fun y bi => ciph (xor bi y)) (ciph b)).take t

/-- §6.1 steps 5–7, `S = S₁ ‖ … ‖ Sₘ` for `m` blocks: `Sⱼ = CIPH_K(Ctrⱼ)`. -/
def keystream (ciph : Cipher) (nonce : List Byte) (m : Nat) : List Byte :=
  (List.range m).flatMap fun j => ciph (ctrBlock nonce (j + 1))

/-- `P ⊕ MSB_Plen(S)` (§6.1 step 8, §6.2 step 5): the text `x` XORed with
the keystream from `Ctr₁`. -/
def crypt (ciph : Cipher) (nonce x : List Byte) : List Byte :=
  xor x (keystream ciph nonce ((x.length + 15) / 16))

/-- `T ⊕ MSB_Tlen(S₀)` (§6.1 step 8, §6.2 step 6): a MAC of `t` bytes XORed
with the first `t` bytes of `S₀ = CIPH_K(Ctr₀)`, which encrypts it or
decrypts it. -/
def cryptTag (ciph : Cipher) (t : Nat) (nonce tag : List Byte) : List Byte :=
  xor tag ((ciph (ctrBlock nonce 0)).take t)

/-- §6.1, generation-encryption, for the MAC length `t` (bytes), of valid
`N`, `P` and `A` (`valid`): the encrypted payload `P ⊕ MSB_Plen(S)` and the
encrypted MAC `T ⊕ MSB_Tlen(S₀)`, whose concatenation is the ciphertext
`C` of step 8. -/
def encryptWith (ciph : Cipher) (t : Nat) (nonce pt aad : List Byte) : List Byte × List Byte :=
  (crypt ciph nonce pt, cryptTag ciph t nonce (mac ciph t nonce aad pt))

/-- §6.2 steps 2–10, decryption-verification, for the MAC length `t`
(bytes), of the ciphertext `C = ct ‖ tag` (`tag` the `t` bytes of the
encrypted MAC) whose `N`, `A` and `P` are valid (step 7): the payload
`P = ct ⊕ MSB_Plen(S)` if the MAC `T = tag ⊕ MSB_Tlen(S₀)` is that of
`(N, A, P)` (step 10), and `none` (INVALID) if not. -/
def decryptWith (ciph : Cipher) (t : Nat) (nonce ct aad tag : List Byte) : Option (List Byte) :=
  let pt := crypt ciph nonce ct
  if cryptTag ciph t nonce tag = mac ciph t nonce aad pt then some pt else none

/-- §6.1, generation-encryption with the MAC length `t` (bytes) of the
payload `pt` with the associated data `aad` under the nonce `nonce`: the
ciphertext `C`, or `none` if the inputs are not valid. -/
def encrypt (ciph : Cipher) (t : Nat) (nonce pt aad : List Byte) : Option (List Byte) :=
  if valid t nonce.length aad.length pt.length then
    let (ct, tag) := encryptWith ciph t nonce pt aad
    some (ct ++ tag)
  else none

/-- §6.2, decryption-verification with the MAC length `t` (bytes) of the
ciphertext `c` with the associated data `aad` under the nonce `nonce`: the
payload, or `none` (INVALID) if `c` is shorter than the MAC (step 1, but see
above), if `N`, `A` or `P` is not valid (step 7) or if the MAC is wrong
(step 10). -/
def decrypt (ciph : Cipher) (t : Nat) (nonce c aad : List Byte) : Option (List Byte) :=
  if c.length < t || !valid t nonce.length aad.length (c.length - t) then none
  else decryptWith ciph t nonce (c.take (c.length - t)) aad (c.drop (c.length - t))

/-! ## AES-CCM -/

/-- `CIPH_K` for AES with `nr` rounds and the key schedule `w` (as bytes). -/
def aesWith (nr : Nat) (w : List Byte) : Cipher := fun x =>
  (Aes.cipher nr w (Vector.ofFn fun i => x.getD i 0)).toList

/-- `CIPH_K` for AES with the key `key` (16, 24 or 32 bytes). -/
def aes (key : List Byte) : Cipher := aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)

/-- AES-CCM generation-encryption, with a MAC of `t` bytes. -/
def aesCcmEncrypt (key : List Byte) (t : Nat) (nonce pt aad : List Byte) : Option (List Byte) :=
  encrypt (aes key) t nonce pt aad

/-- AES-CCM decryption-verification, with a MAC of `t` bytes. -/
def aesCcmDecrypt (key : List Byte) (t : Nat) (nonce c aad : List Byte) : Option (List Byte) :=
  decrypt (aes key) t nonce c aad

/-! ## On memory -/

/-- `CIPH_K` for AES with `nr` rounds and the key schedule in the first
`16 (nr + 1)` bytes at `p` (as `vg_aes_expand_key` writes it). -/
def ctxCiph (m : Mem) (p : Addr) (nr : Nat) : Cipher :=
  aesWith nr (Aes.bytesAt m p (16 * (nr + 1)))

/-- The key schedule of `key`, for its number of rounds, has the cipher of
AES with `key`. -/
theorem ctxCiph_eq {m : Mem} {p : Addr} {key : List Byte}
    (hk : Aes.bytesAt m p (16 * (Aes.rounds (key.length / 4) + 1)) = Aes.expandKey key) :
    ctxCiph m p (Aes.rounds (key.length / 4)) = aes key := by
  rw [ctxCiph, hk, aes]

end VG.Spec.Ccm

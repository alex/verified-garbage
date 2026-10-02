import VerifiedGarbage.Spec.Aes

/-!
# GCM (NIST SP 800-38D)

**Trusted** (as every file in `Spec/`). The Galois/Counter Mode of a 128-bit
block cipher, transcribed from NIST SP 800-38D, *Recommendation for Block
Cipher Modes of Operation: Galois/Counter Mode (GCM) and GMAC* (November
2007); section numbers below refer to it. Bit strings are sequences of whole
bytes here: every length (of the IV, the plaintext, the additional
authenticated data and the tag) is a multiple of 8 bits, as every
implementation we test against requires.

A 128-bit block is a `BitVec 128` whose most significant bit is the
leftmost bit of the string (§4.2.2, "the leftmost bit … is the most
significant"): the first byte of a block is its most significant byte.

Two kinds of functions are implemented in assembly; their contracts are in
`Spec/Gcm/Contract.lean`:

* the primitives: the multiplication-and-add steps of `GHASH` over whole
  blocks (`ghashFrom`), and counter mode over whole blocks with `inc₃₂`
  (`ctr32`, the core of `GCTR`);
* the whole of AES-GCM: the key setup (the key schedule and the hash subkey,
  "The key context" below), one-shot GCM-AE and GCM-AD (`encryptWith`,
  `decryptWith`), and the same over a message given in pieces ("Streaming"
  below).

The tag lengths GCM supports (§5.2.1.2) are `tagLenOk`. The limits on the
other lengths (§5.2.1.1, `supported`) concern a whole message, which a
streaming caller gives in pieces; the caller checks them.
-/

namespace VG.Spec.Gcm

/-- A 128-bit block (§4.2.2): the leftmost bit is the most significant. -/
abbrev Block := BitVec 128

/-- The block of 16 bytes, the first byte the most significant. -/
def ofBytes (bs : List Byte) : Block :=
  BitVec.ofNat 128 (bs.foldl (fun acc b => 256 * acc + b.toNat) 0)

/-- The 16 bytes of a block, the most significant first. -/
def toBytes (x : Block) : List Byte :=
  (List.range 16).map fun i => x.extractLsb' (8 * (15 - i)) 8

/-! ## Mathematical components (§6) -/

/-- §6.2, `inc₃₂(X) = MSB₉₆(X) ‖ [int(LSB₃₂(X)) + 1 mod 2³²]₃₂`: the
rightmost 32 bits, as an integer, incremented modulo 2³². -/
def inc32 (x : Block) : Block :=
  (x.extractLsb' 32 96 ++ (x.extractLsb' 0 32 + 1) : BitVec (96 + 32))

/-- §6.3, the constant `R = 11100001 ‖ 0¹²⁰`. -/
def R : Block := 0xE1 <<< 120

/-- §6.3, the product `X • Y` of two blocks (Algorithm 1). With `x₀ x₁ …
x₁₂₇` the bits of `X` from the left, `Z₀ = 0¹²⁸` and `V₀ = Y`, for `i` from
0 to 127:
```
Zᵢ₊₁ = Zᵢ           if xᵢ = 0
       Zᵢ ⊕ Vᵢ      if xᵢ = 1
Vᵢ₊₁ = Vᵢ >> 1       if LSB₁(Vᵢ) = 0
       (Vᵢ >> 1) ⊕ R if LSB₁(Vᵢ) = 1
```
and the product is `Z₁₂₈`. -/
def mul (x y : Block) : Block :=
  ((List.range 128).foldl (fun (zv : Block × Block) i =>
    let (z, v) := zv
    let z := if x.getMsbD i then z ^^^ v else z
    let v := if v.getLsbD 0 then (v >>> 1) ^^^ R else v >>> 1
    (z, v)) (0, y)).1

/-- §6.4, `GHASH_H` (Algorithm 2) continued from `Y` over the blocks `X`:
`Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H`. `GHASH_H(X)` itself starts from `Y₀ = 0¹²⁸`. -/
def ghashFrom (h y : Block) (xs : List Block) : Block :=
  xs.foldl (fun y x => mul (y ^^^ x) h) y

/-- §6.4, `GHASH_H(X)` of a string of whole blocks. -/
def ghash (h : Block) (xs : List Block) : Block := ghashFrom h 0 xs

/-- The blocks of a byte string whose length is a multiple of 16. -/
def blocks (bs : List Byte) : List Block :=
  (List.range (bs.length / 16)).map fun i => ofBytes ((bs.drop (16 * i)).take 16)

/-- The keystream of counter mode with `inc₃₂`, as §6.5 steps 5–6 compute it
for `GCTR`: the cipher applied to the counter blocks `CB₁ = ICB`,
`CBᵢ = inc₃₂(CBᵢ₋₁)`, `n` of them. -/
def keystream (ciph : Block → Block) (icb : Block) (n : Nat) : List Block :=
  (List.range n).map fun i => ciph (Nat.repeat inc32 i icb)

/-- §6.5 steps 5–7 on whole blocks: `Yᵢ = Xᵢ ⊕ CIPH_K(CBᵢ)`. -/
def ctr32 (ciph : Block → Block) (icb : Block) (xs : List Block) : List Block :=
  List.zipWith (· ^^^ ·) xs (keystream ciph icb xs.length)

/-- §6.5, `GCTR_K(ICB, X)` (Algorithm 3), on a byte string: counter mode on
the whole blocks, and for a final partial block `Xₙ*`,
`Yₙ* = Xₙ* ⊕ MSB_len(Xₙ*)(CIPH_K(CBₙ))`. The empty string gives the empty
string (step 1). -/
def gctr (ciph : Block → Block) (icb : Block) (x : List Byte) : List Byte :=
  let n := (x.length + 15) / 16
  let ks := (keystream ciph icb n).flatMap toBytes
  List.zipWith (· ^^^ ·) x ks

/-! ## GCM-AE and GCM-AD (§7) -/

/-- `0ˢ` for `s` a multiple of 8: `s / 8` zero bytes. -/
def zeros (nBytes : Nat) : List Byte := List.replicate nBytes 0

/-- `[x]₆₄`: the 64-bit big-endian representation of `x` (modulo 2⁶⁴). -/
def be64 (x : Nat) : List Byte := (List.range 8).map fun i => BitVec.ofNat 8 (x / 256 ^ (7 - i))

/-- The number of zero bytes that pad a string of `len` bytes to a multiple
of 16 bytes (`u / 8` or `v / 8` in §7.1: `128 ⌈len(C)/128⌉ − len(C)`). -/
def padLen (len : Nat) : Nat := (16 - len % 16) % 16

/-- §7.1 step 2, the pre-counter block `J₀`: `IV ‖ 0³¹ ‖ 1` if `len(IV) = 96`,
and otherwise, with `s = 128 ⌈len(IV)/128⌉ − len(IV)`,
`GHASH_H(IV ‖ 0^(s+64) ‖ [len(IV)]₆₄)`. -/
def j0 (h : Block) (iv : List Byte) : Block :=
  if iv.length = 12 then ofBytes (iv ++ [0, 0, 0, 1])
  else ghash h (blocks (iv ++ zeros (padLen iv.length + 8) ++ be64 (8 * iv.length)))

/-- §7.1 step 5, the block string whose `GHASH` is `S`:
`A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ [len(A)]₆₄ ‖ [len(C)]₆₄`. -/
def authBlocks (a c : List Byte) : List Block :=
  blocks (a ++ zeros (padLen a.length) ++ c ++ zeros (padLen c.length) ++
    be64 (8 * a.length) ++ be64 (8 * c.length))

/-- §7.1, `GCM-AE_K(IV, P, A)` (Algorithm 4), for the block cipher `ciph`
(`CIPH_K`) and a tag of `t` bytes, returning `(C, T)`:
```
1. H = CIPH_K(0¹²⁸)
2. J₀ as in `j0`
3. C = GCTR_K(inc₃₂(J₀), P)
4–5. S = GHASH_H(A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)
6. T = MSB_t(GCTR_K(J₀, S))
```
The lengths must be supported (§5.2.1.1: `len(P) ≤ 2³⁹ − 256`,
`len(A) ≤ 2⁶⁴ − 1`, `1 ≤ len(IV) ≤ 2⁶⁴ − 1` bits), which is the caller's
obligation. -/
def encrypt (ciph : Block → Block) (t : Nat) (iv p a : List Byte) : List Byte × List Byte :=
  let h := ciph 0
  let j := j0 h iv
  let c := gctr ciph (inc32 j) p
  let s := ghash h (authBlocks a c)
  (c, (gctr ciph j (toBytes s)).take t)

/-- Whether the bit lengths of the IV, the ciphertext and the additional
authenticated data are supported (§5.2.1.1), for byte strings of these
lengths. -/
def supported (ivLen cLen aLen : Nat) : Bool :=
  1 ≤ 8 * ivLen && 8 * ivLen ≤ 2 ^ 64 - 1 && 8 * cLen ≤ 2 ^ 39 - 256 && 8 * aLen ≤ 2 ^ 64 - 1

/-- §7.2, `GCM-AD_K(IV, C, A, T)` (Algorithm 5), for the block cipher `ciph`
and a tag length of `t` bytes: `none` (FAIL) if a length is not supported
or `len(T) ≠ t` (step 1), otherwise the plaintext `P = GCTR_K(inc₃₂(J₀), C)`
if the tag `T' = MSB_t(GCTR_K(J₀, S))` equals `T`, and `none` if not. -/
def decrypt (ciph : Block → Block) (t : Nat) (iv c a tag : List Byte) : Option (List Byte) :=
  if !supported iv.length c.length a.length || tag.length ≠ t then none
  else
    let h := ciph 0
    let j := j0 h iv
    let p := gctr ciph (inc32 j) c
    let s := ghash h (authBlocks a c)
    if (gctr ciph j (toBytes s)).take t = tag then some p else none

/-! ## With the hash subkey given

An implementation computes the hash subkey `H = CIPH_K(0¹²⁸)` (§7.1 step 1,
§7.2 step 2) once per key, stores it, and uses the stored value: GCM-AE and
GCM-AD for a given `H` are `encryptWith` and `decryptWith`, and `encrypt`
and `decrypt` are those with `H = CIPH_K(0¹²⁸)` (`encrypt_eq`,
`decrypt_eq`, which hold by definition). -/

/-- §7.1 steps 2 and 4–6 (§7.2 steps 3 and 5–7), before the truncation
`MSB_t`, for the hash subkey `h`: the 16-byte block `GCTR_K(J₀, S)`, where
`S = GHASH_H(A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)`, of the ciphertext
`c` and the additional data `a` under the IV `iv`. The tag of `t` bytes is
its first `t` bytes. -/
def fullTag (ciph : Block → Block) (h : Block) (iv a c : List Byte) : List Byte :=
  gctr ciph (j0 h iv) (toBytes (ghash h (authBlocks a c)))

/-- §7.1 steps 2–6, `GCM-AE_K(IV, P, A)` for the hash subkey `h` and a tag
of `t` bytes: `C = GCTR_K(inc₃₂(J₀), P)` and `T = MSB_t(GCTR_K(J₀, S))`. -/
def encryptWith (ciph : Block → Block) (h : Block) (t : Nat) (iv p a : List Byte) :
    List Byte × List Byte :=
  let c := gctr ciph (inc32 (j0 h iv)) p
  (c, (fullTag ciph h iv a c).take t)

/-- GCM-AE is `encryptWith` for the hash subkey `CIPH_K(0¹²⁸)`. -/
theorem encrypt_eq (ciph : Block → Block) (t : Nat) (iv p a : List Byte) :
    encrypt ciph t iv p a = encryptWith ciph (ciph 0) t iv p a := rfl

/-- §7.2 steps 3–8, `GCM-AD_K(IV, C, A, T)` for the hash subkey `h` and a
tag length of `t` bytes, once step 1 has accepted the lengths: the plaintext
`P = GCTR_K(inc₃₂(J₀), C)` if `T' = MSB_t(GCTR_K(J₀, S))` is `tag`, and
`none` (FAIL) if not. -/
def decryptWith (ciph : Block → Block) (h : Block) (t : Nat) (iv c a tag : List Byte) :
    Option (List Byte) :=
  if (fullTag ciph h iv a c).take t = tag then some (gctr ciph (inc32 (j0 h iv)) c) else none

/-- GCM-AD is step 1 (the lengths) followed by `decryptWith` for the hash
subkey `CIPH_K(0¹²⁸)`. -/
theorem decrypt_eq (ciph : Block → Block) (t : Nat) (iv c a tag : List Byte) :
    decrypt ciph t iv c a tag =
      if !supported iv.length c.length a.length || tag.length ≠ t then none
      else decryptWith ciph (ciph 0) t iv c a tag := rfl

/-- §5.2.1.2: whether GCM supports a tag of `t` bytes: 128, 120, 112, 104 or
96 bits, or, "for certain applications", 64 or 32 bits (whose use Appendix C
restricts further). -/
def tagLenOk (t : Nat) : Bool := t == 4 || t == 8 || (12 ≤ t && t ≤ 16)

/-! ## AES-GCM -/

/-- `CIPH_K` for AES with `nr` rounds and the key schedule `w` (as bytes). -/
def aesWith (nr : Nat) (w : List Byte) (x : Block) : Block :=
  ofBytes (Aes.cipher nr w (Vector.ofFn fun i => (toBytes x).getD i 0)).toList

/-- `CIPH_K` for AES with the key `key` (16, 24 or 32 bytes). -/
def aes (key : List Byte) : Block → Block :=
  aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)

/-- AES-GCM authenticated encryption, with a tag of `t` bytes. -/
def aesGcmEncrypt (key : List Byte) (t : Nat) (iv p a : List Byte) : List Byte × List Byte :=
  encrypt (aes key) t iv p a

/-- AES-GCM authenticated decryption, with a tag of `t` bytes. -/
def aesGcmDecrypt (key : List Byte) (t : Nat) (iv c a tag : List Byte) : Option (List Byte) :=
  decrypt (aes key) t iv c a tag

/-! ## On memory -/

/-- The block of the 16 bytes at `p`. -/
def blockAt (m : Mem) (p : Addr) : Block := ofBytes (Aes.bytesAt m p 16)

/-- The `n` blocks at `p`. -/
def blocksAt (m : Mem) (p : Addr) (n : Nat) : List Block :=
  (List.range n).map fun i => blockAt m (p + BitVec.ofNat 64 (16 * i))

/-! ## The key context

`vg_aes_gcm_init` stores what AES-GCM needs of a key in a 256-byte key
context, which the other AES-GCM functions read:

* bytes 0 to `16 (Nr + 1) − 1`: the AES key schedule for `Nr` rounds, as
  `vg_aes_expand_key` writes it (`Aes.expandKey`);
* bytes 240–255: the hash subkey `H = CIPH_K(0¹²⁸)` (§7.1 step 1).

The bytes between them (for 10 or 12 rounds) are unspecified. The functions
that read a key context compute with the hash subkey stored in it (`ctxH`)
and, those that need the cipher, with the cipher it stores for the number of
rounds `Nr` they take as an argument, which is public (`ctxCiph`), whatever
the context holds: for a context that
`vg_aes_gcm_init` wrote for `key` (`KeyRepr`), that is AES-GCM with `key`
(`encryptWith_ctx`, `decryptWith_ctx`). -/

/-- The cipher of the key context at `p` for `nr` rounds: AES with `nr`
rounds and the key schedule in its first `16 (nr + 1)` bytes. -/
def ctxCiph (m : Mem) (p : Addr) (nr : Nat) : Block → Block :=
  aesWith nr (Aes.bytesAt m p (16 * (nr + 1)))

/-- The hash subkey of the key context at `p`: its bytes 240–255. -/
def ctxH (m : Mem) (p : Addr) : Block := blockAt m (p + 240)

/-- The key context at `p` is that of the AES key `key`: it holds the key
schedule of `key` and the hash subkey `CIPH_K(0¹²⁸)`. -/
def KeyRepr (m : Mem) (p : Addr) (key : List Byte) : Prop :=
  Aes.bytesAt m p (16 * (Aes.rounds (key.length / 4) + 1)) = Aes.expandKey key ∧
    ctxH m p = aes key 0

/-- GCM-AE with the key context of `key`, for its number of rounds, is
AES-GCM's with `key`. -/
theorem encryptWith_ctx {m : Mem} {p : Addr} {key : List Byte} (hk : KeyRepr m p key)
    (t : Nat) (iv pt a : List Byte) :
    encryptWith (ctxCiph m p (Aes.rounds (key.length / 4))) (ctxH m p) t iv pt a =
      aesGcmEncrypt key t iv pt a := by
  unfold ctxCiph
  rw [hk.1, hk.2]
  rfl

/-- GCM-AD with the key context of `key`, for its number of rounds, is
AES-GCM's with `key`, for lengths that step 1 accepts. -/
theorem decryptWith_ctx {m : Mem} {p : Addr} {key : List Byte} (hk : KeyRepr m p key)
    (t : Nat) (iv c a tag : List Byte)
    (hs : supported iv.length c.length a.length = true) (ht : tag.length = t) :
    decryptWith (ctxCiph m p (Aes.rounds (key.length / 4))) (ctxH m p) t iv c a tag =
      aesGcmDecrypt key t iv c a tag := by
  unfold ctxCiph
  rw [hk.1, hk.2, aesGcmDecrypt, decrypt_eq, hs, ht]
  simp only [Bool.not_true, Bool.false_or, ne_eq, not_true_eq_false, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## Streaming

The streaming functions encrypt or decrypt a message given in pieces: all of
its additional data `A`, then its text, each in pieces of any length. Their
state, 80 bytes, holds everything secret that GCM-AE or GCM-AD keeps from
one piece to the next (`StreamRepr`). What is public, the lengths of `A` and
of the text so far, the caller keeps and passes to each function, as it does
the key context.

GHASH absorbs `A ‖ 0ᵛ ‖ C` (§7.1 step 5) as it arrives (`ghashInput`), whole
blocks into the accumulator `Y` and the rest buffered; the zero padding `0ᵛ`
follows `A` once the ciphertext `C` has begun. Counter mode (§6.5) XORs the
keystream `CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …`, from `CB₁ = inc₃₂(J₀)`, into the
text: the state holds the next counter block, and the keystream block of
the last block of `C` if that is partial, whose bytes not used yet the next
piece of text uses.

A state that represents the message with the IV `iv`, the additional data
`a` and the ciphertext `c` so far gives the tag `fullTag ciph h iv a c` (§7.1
steps 5–6, §7.2 steps 6–7, untruncated): that of GCM-AE (`encryptWith`)
when `c` is the encryption `gctr ciph (inc32 (j0 h iv)) p` of the plaintext
`p` given so far, and the one GCM-AD compares (`decryptWith`). -/

/-- The string GHASH absorbs (§7.1 step 5) for the additional data `a` and
the ciphertext `c` so far, before the last zero padding and the lengths:
`A` alone while there is no ciphertext, and `A ‖ 0ᵛ ‖ C` once there is.
(`authBlocks a c` is the blocks of `ghashInput a c`, padded with zeros to a
whole number of blocks, followed by `[len(A)]₆₄ ‖ [len(C)]₆₄`.) -/
def ghashInput (a c : List Byte) : List Byte :=
  if c = [] then a else a ++ zeros (padLen a.length) ++ c

/-- The streaming state at `p` represents a message with the IV `iv`, the
additional data `a` and the ciphertext `c` so far, for the cipher `ciph`
and the hash subkey `h`. With `x = ghashInput a c`, of which GHASH has
absorbed the whole blocks, and `ICB = inc₃₂(J₀)` the first counter block
(§7.1 step 3):

* bytes 0–15: `J₀` (§7.1 step 2);
* bytes 16–31: `GHASH_H` of the whole blocks of `x`;
* bytes 32–47: the last `len(x) mod 16` bytes of `x`, which do not fill a
  block, followed by unspecified bytes;
* bytes 48–63: the next counter block, `inc₃₂ᵏ(ICB)` for the number
  `k = ⌈len(C)/128⌉` of counter blocks used;
* bytes 64–79: if `c` ends in a partial block, the keystream block
  `CIPH_K(inc₃₂ʲ(ICB))` of that block, `j = ⌊len(C)/128⌋` (the block of
  `keystream ciph ICB` that `gctr` XORs into it); unspecified otherwise. -/
def StreamRepr (m : Mem) (p : Addr) (ciph : Block → Block) (h : Block) (iv a c : List Byte) :
    Prop :=
  let j := j0 h iv
  let icb := inc32 j
  let x := ghashInput a c
  let n := 16 * (x.length / 16)
  blockAt m p = j ∧
    blockAt m (p + 16) = ghash h (blocks (x.take n)) ∧
    Aes.bytesAt m (p + 32) (x.length % 16) = x.drop n ∧
    blockAt m (p + 48) = Nat.repeat inc32 ((c.length + 15) / 16) icb ∧
    (c.length % 16 ≠ 0 → blockAt m (p + 64) = ciph (Nat.repeat inc32 (c.length / 16) icb))

end VG.Spec.Gcm

import VerifiedGarbage.TCB.Mem

/-!
# AES (FIPS 197)

**Trusted** (as every file in `Spec/`). The block cipher AES (the forward
cipher only, which is all that GCM uses), transcribed from FIPS 197,
*Advanced Encryption Standard (AES)* (November 2001, updated May 2023);
section numbers below refer to it. Keys of 128, 192 and 256 bits are
covered (`Nk = 4, 6, 8` words, `Nr = Nk + 6` rounds, §5).

The state (§3.4) is a 4×4 array of bytes `s[r, c]`; it is represented as
the 16 bytes of the input in order, so `s[r, c]` is byte `r + 4c`, as §3.4
fills it (`s[r, c] = in[r + 4c]`). A word of the key schedule is 4 bytes
`w[i] = (w[i]₀, …, w[i]₃)`, and the round key of round `j` is the words
`w[4j] … w[4j + 3]`, so as bytes it is the 16 bytes `16j … 16j + 15` of the
schedule, lining up with the state: `AddRoundKey` XORs byte `r + 4c` of the
round key into `s[r, c]` (§5.1.4).

The S-box is defined as §5.1.1 does, by the multiplicative inverse in
GF(2⁸) followed by an affine transformation, rather than by copying the
table of Figure 7; the known-answer tests in `VerifiedGarbageTest/Aes.lean`
check the result.

The primitives implemented in assembly are the key expansion and GCM's
counter mode (`Spec/Gcm.lean`); their contracts are in
`Spec/Aes/Contract.lean` and `Spec/Gcm/Contract.lean`.
-/

namespace VG.Spec.Aes

/-! ## Arithmetic in GF(2⁸) (§4) -/

/-- §4.2, `XTIMES(b)`: multiplication by `x` modulo the reduction
polynomial `m(x) = x⁸ + x⁴ + x³ + x + 1`: shift left by one bit, and if the
bit shifted out was 1, XOR with `{1b}`. -/
def xtimes (b : Byte) : Byte := (b <<< 1) ^^^ (if b.msb then 0x1b else 0)

/-- §4.2, the product `b • c` in GF(2⁸): the sum (XOR) of `XTIMES` applied
`i` times to `c`, for each bit `i` of `b` that is 1. -/
def mul (b c : Byte) : Byte :=
  (List.range 8).foldl (fun acc i => if b.getLsbD i then acc ^^^ Nat.repeat xtimes i c else acc) 0

/-- `b` raised to the power `n < 2⁸` in GF(2⁸): the product of the powers
`b^(2^i)` (obtained by repeated squaring) for each bit `i` of `n` that is 1. -/
def pow (b : Byte) (n : Nat) : Byte :=
  ((List.range 8).foldl (fun (acc, sq) i => (if n.testBit i then mul acc sq else acc, mul sq sq))
    ((1 : Byte), b)).1

/-- §4.4, the multiplicative inverse `b⁻¹ = b²⁵⁴` of a nonzero `b`, and
`{00}` for `{00}` (which §5.1.1 maps to itself). -/
def inv (b : Byte) : Byte := pow b 254

/-! ## The cipher's transformations (§5.1) -/

/-- The state (§3.4): `s[r, c]` is byte `r + 4c`. -/
abbrev State := Vector Byte 16

/-- §5.1.1, the S-box: `b ↦ b⁻¹` (with `{00} ↦ {00}`), followed by the
affine transformation:
`b'ᵢ = bᵢ ⊕ b₍ᵢ₊₄₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₆₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ cᵢ`,
where `c = {63}` and `bᵢ` is bit `i` (bit 0 the least significant). -/
def sbox (b : Byte) : Byte :=
  let b := inv b
  let c : Byte := 0x63
  let bit (i : Nat) : Bool :=
    b.getLsbD i ^^ b.getLsbD ((i + 4) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^
      b.getLsbD ((i + 6) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ c.getLsbD i
  BitVec.ofNat 8 ((List.range 8).foldl (fun acc i => acc + if bit i then 2 ^ i else 0) 0)

/-- §5.1.1, `SUBBYTES`: the S-box applied to every byte of the state. -/
def subBytes (s : State) : State := s.map sbox

/-- §5.1.2, `SHIFTROWS`: `s'[r, c] = s[r, (c + r) mod 4]`. -/
def shiftRows (s : State) : State :=
  Vector.ofFn fun (i : Fin 16) =>
    let r := i.1 % 4; let c := i.1 / 4
    s.getD (r + 4 * ((c + r) % 4)) 0

/-- §5.1.3, `MIXCOLUMNS`, on each column `c`:
```
s'[0, c] = ({02} • s[0, c]) ⊕ ({03} • s[1, c]) ⊕ s[2, c] ⊕ s[3, c]
s'[1, c] = s[0, c] ⊕ ({02} • s[1, c]) ⊕ ({03} • s[2, c]) ⊕ s[3, c]
s'[2, c] = s[0, c] ⊕ s[1, c] ⊕ ({02} • s[2, c]) ⊕ ({03} • s[3, c])
s'[3, c] = ({03} • s[0, c]) ⊕ s[1, c] ⊕ s[2, c] ⊕ ({02} • s[3, c])
``` -/
def mixColumns (s : State) : State :=
  Vector.ofFn fun (i : Fin 16) =>
    let r := i.1 % 4; let c := i.1 / 4
    let a (k : Nat) : Byte := s.getD ((r + k) % 4 + 4 * c) 0
    mul 0x02 (a 0) ^^^ mul 0x03 (a 1) ^^^ a 2 ^^^ a 3

/-- §5.1.4, `ADDROUNDKEY`: XOR the round key (16 bytes, in the order of the
state's bytes) into the state. -/
def addRoundKey (s : State) (rk : List Byte) : State :=
  Vector.ofFn fun (i : Fin 16) => s.getD i 0 ^^^ rk.getD i 0

/-! ## Key expansion (§5.2) -/

/-- The number of rounds `Nr` for a key of `Nk` words (§5). -/
def rounds (nk : Nat) : Nat := nk + 6

/-- A word of the key schedule: 4 bytes. -/
abbrev Word := List Byte

/-- §5.2, `SUBWORD`: the S-box applied to each byte of a word. -/
def subWord (w : Word) : Word := w.map sbox

/-- §5.2, `ROTWORD([a₀, a₁, a₂, a₃]) = [a₁, a₂, a₃, a₀]`. -/
def rotWord (w : Word) : Word := w.drop 1 ++ w.take 1

/-- §5.2, the round constant `Rcon[j] = [x^(j−1), {00}, {00}, {00}]`, `x^(j−1)`
being `XTIMES` applied `j − 1` times to `{01}` (§5.2 lists them). -/
def rcon (j : Nat) : Word := [Nat.repeat xtimes (j - 1) 1, 0, 0, 0]

/-- Word-wise XOR. -/
def xorWord (a b : Word) : Word := List.zipWith (· ^^^ ·) a b

/-- §5.2, `KEYEXPANSION` (Algorithm 2), the words `w[0] … w[i − 1]` (for
`i ≥ Nk`) of the schedule of the `Nk`-word key `key` (4·`Nk` bytes):
```
w[i] = key[4i .. 4i + 3]                            for i < Nk
temp = w[i − 1]
if i mod Nk = 0:           temp = SUBWORD(ROTWORD(temp)) ⊕ Rcon[i / Nk]
else if Nk > 6 and i mod Nk = 4: temp = SUBWORD(temp)
w[i] = w[i − Nk] ⊕ temp
``` -/
def expandWords (key : List Byte) (nk : Nat) : Nat → List Word
  | 0 => []
  | i + 1 =>
    let ws := expandWords key nk i
    if i < nk then ws ++ [(key.drop (4 * i)).take 4]
    else
      let temp := ws.getD (i - 1) []
      let temp :=
        if i % nk = 0 then xorWord (subWord (rotWord temp)) (rcon (i / nk))
        else if nk > 6 ∧ i % nk = 4 then subWord temp
        else temp
      ws ++ [xorWord (ws.getD (i - nk) []) temp]

/-- §5.2, the key schedule of a key of 16, 24 or 32 bytes: the
`4 (Nr + 1)` words, as `16 (Nr + 1)` bytes. -/
def expandKey (key : List Byte) : List Byte :=
  let nk := key.length / 4
  (expandWords key nk (4 * (rounds nk + 1))).flatten

/-! ## The cipher (§5.1) -/

/-- The round key of round `j` (16 bytes) of the key schedule `w` (as bytes). -/
def roundKey (w : List Byte) (j : Nat) : List Byte := (w.drop (16 * j)).take 16

/-- §5.1, `CIPHER(in, Nr, w)` (Algorithm 1), on the key schedule `w` given
as bytes:
```
state ← ADDROUNDKEY(in, w[0..3])
for round from 1 to Nr − 1:
  state ← ADDROUNDKEY(MIXCOLUMNS(SHIFTROWS(SUBBYTES(state))), w[4·round .. 4·round + 3])
state ← ADDROUNDKEY(SHIFTROWS(SUBBYTES(state)), w[4·Nr .. 4·Nr + 3])
``` -/
def cipher (nr : Nat) (w : List Byte) (input : State) : State :=
  let s := addRoundKey input (roundKey w 0)
  let s := (List.range (nr - 1)).foldl
    (fun s j => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (j + 1))) s
  addRoundKey (shiftRows (subBytes s)) (roundKey w nr)

/-- AES encryption of the 16-byte block `input` under the key `key` (16,
24 or 32 bytes). -/
def encrypt (key : List Byte) (input : List Byte) : List Byte :=
  (cipher (rounds (key.length / 4)) (expandKey key) (Vector.ofFn fun i => input.getD i 0)).toList

/-! ## On memory -/

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

end VG.Spec.Aes

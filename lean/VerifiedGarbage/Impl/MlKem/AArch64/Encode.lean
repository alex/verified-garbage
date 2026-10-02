import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-KEM on AArch64: encoding, decoding and sampling from bytes

* `encode12(f = x0, out = x1)`: `ByteEncode₁₂`, 3 bytes per pair of
  coefficients `f₀, f₁`: `f₀`, `⌊f₀ / 2⁸⌋ + 2⁴ f₁` and `⌊f₁ / 2⁴⌋`, each
  stored by `strb` (its low byte).
* `decode12(b = x0, f = x1)`: `ByteDecode₁₂`, 2 coefficients per 3 bytes
  `b₀, b₁, b₂`: `b₀ + 2⁸ (b₁ mod 2⁴)` and `⌊b₁ / 2⁴⌋ + 2⁴ b₂`, each less than
  `2¹²` and reduced modulo `q` with one conditional subtraction.
* `cbd2(b = x0, f = x1)`: `SamplePolyCBD₂`, 2 coefficients per byte `b`:
  `s = (b & 0x55) + ((b >> 1) & 0x55)` holds the sums of the pairs of bits
  of `b` in its four 2-bit fields `x₀, y₀, x₁, y₁`, and coefficient `j` is
  `(xⱼ + q - yⱼ) mod q`.

* `checkEk(ek = x0) -> w0`: the modulus check of ML-KEM-768 (and, with
  `checkEkWith 512`, of ML-KEM-1024): for each of the 384 (512) groups of
  3 bytes of `ek[0 : 1152]` (`ek[0 : 1536]`), its two 12-bit fields `f`
  (as in `decode12`), each counted in `x10` if `q - 1 - f` is negative;
  returns 1 if the count is 0 (`x10 - 1` negative), and 0 otherwise.

Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-! ## `encode12` -/

def encode12Body : List Instr :=
  [.ldr .w .x9 .x0 0, .ldr .w .x10 .x0 4, .strb .x9 .x1 0, .lsr .x .x11 .x9 8, .lsl .x .x12 .x10 4,
    .add .x .x11 .x11 .x12, .strb .x11 .x1 1, .lsr .x .x12 .x10 4, .strb .x12 .x1 2,
    .addImm .x .x0 .x0 8, .addImm .x .x1 .x1 3, .subImm .x .x13 .x13 1]

def encode12 : Prog isa :=
  .seq (.block [.movz .x .x13 128 0]) (.loop (.block encode12Body) (.nonzero .x .x13))

/-! ## `decode12` -/

def decode12Body : List Instr :=
  [.ldrb .x9 .x0 0, .ldrb .x10 .x0 1, .ldrb .x11 .x0 2,
    .logic .and .x .x12 .x10 .x14, .lsl .x .x12 .x12 8, .add .x .x12 .x12 .x9] ++
  csub .x12 .x13 .x15 ++
  ([.str .w .x12 .x1 0, .lsr .x .x12 .x10 4, .lsl .x .x13 .x11 4, .add .x .x12 .x12 .x13] :
    List Instr) ++
  csub .x12 .x13 .x15 ++
  ([.str .w .x12 .x1 4, .addImm .x .x0 .x0 3, .addImm .x .x1 .x1 8, .subImm .x .x16 .x16 1] :
    List Instr)

def decode12 : Prog isa :=
  .seq (.block [.movz .x .x14 15 0, .movz .x .x15 3329 0, .movz .x .x16 128 0])
    (.loop (.block decode12Body) (.nonzero .x .x16))

/-! ## `cbd2` -/

def cbd2Body : List Instr :=
  [.ldrb .x9 .x0 0, .lsr .x .x10 .x9 1, .logic .and .x .x9 .x9 .x14,
    .logic .and .x .x10 .x10 .x14, .add .x .x9 .x9 .x10,
    .logic .and .x .x10 .x9 .x15, .lsr .x .x11 .x9 2, .logic .and .x .x11 .x11 .x15,
    .add .x .x10 .x10 .x12, .sub .x .x10 .x10 .x11] ++
  csub .x10 .x13 .x12 ++
  ([.str .w .x10 .x1 0, .lsr .x .x10 .x9 4, .logic .and .x .x10 .x10 .x15, .lsr .x .x11 .x9 6,
    .add .x .x10 .x10 .x12, .sub .x .x10 .x10 .x11] : List Instr) ++
  csub .x10 .x13 .x12 ++
  ([.str .w .x10 .x1 4, .addImm .x .x0 .x0 1, .addImm .x .x1 .x1 8, .subImm .x .x16 .x16 1] :
    List Instr)

def cbd2 : Prog isa :=
  .seq (.block [.movz .x .x14 0x55 0, .movz .x .x15 3 0, .movz .x .x12 3329 0,
      .movz .x .x16 128 0])
    (.loop (.block cbd2Body) (.nonzero .x .x16))

/-! ## `checkEk` -/

def checkEkBody : List Instr :=
  [.ldrb .x12 .x0 0, .ldrb .x13 .x0 1,
    .logic .and .x .x15 .x13 .x14, .lsl .x .x15 .x15 8, .add .x .x15 .x15 .x12,
    .sub .x .x15 .x9 .x15, .lsr .x .x15 .x15 63, .add .x .x10 .x10 .x15,
    .ldrb .x12 .x0 2,
    .lsr .x .x13 .x13 4, .lsl .x .x12 .x12 4, .add .x .x13 .x13 .x12,
    .sub .x .x13 .x9 .x13, .lsr .x .x13 .x13 63, .add .x .x10 .x10 .x13,
    .addImm .x .x0 .x0 3, .subImm .x .x11 .x11 1]

/-- The check of the `n` groups of a key's `3n` bytes. -/
def checkEkWith (n : Nat) : Prog isa :=
  .seq (.block [.movz .x .x9 3328 0, .movz .x .x10 0 0, .movz .x .x11 (BitVec.ofNat 16 n) 0,
      .movz .x .x14 15 0]) <|
  .seq (.loop (.block checkEkBody) (.nonzero .x .x11))
    (.block [.subImm .x .x0 .x10 1, .lsr .x .x0 .x0 63])

/-- The check of ML-KEM-768 (`k = 3`): 384 groups. -/
abbrev checkEk : Prog isa := checkEkWith 384

end VG.Impl.MlKem.AArch64

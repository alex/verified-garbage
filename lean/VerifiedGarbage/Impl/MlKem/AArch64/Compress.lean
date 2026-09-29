import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-KEM on AArch64: compression with encoding, and decoding with decompression

`ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d` for the widths
`d` = 1, 4 and 10 of ML-KEM-768, by one loop over groups of `c`
coefficients and `nb` bytes (`d · c = 8 · nb`: 8 coefficients per byte, 2
per byte, 4 per 5 bytes), whose bits are the same: a group is the
little-endian number whose base-`2ᵈ` digits are its coefficients and whose
bytes are its bytes, built in `x9` (at most 40 bits).

* `compressEncode(f = x0, d = w1, out = x2, len = x3)`: for each group, the
  sum of `Compress_d(f[c g + e]) << d e`, then its bytes. `Compress_d(x)` is
  `((x · M_d + 262080) >> 19) mod 2ᵈ` (`M_d` in `x5`, 262080 in `x6`,
  `2ᵈ - 1` in `x7`).
* `decodeDecompress(b = x0, len = x1, d = w2, f = x3)`: for each group, the
  sum of its bytes `<< 8 j`, then `Decompress_d` of each digit
  `(x9 >> d e) mod 2ᵈ`: `(q · y + 2ᵈ⁻¹) >> d` (`q` in `x5`, `2ᵈ⁻¹` in `x6`,
  `2ᵈ - 1` in `x7`).

The width is chosen by `len` (32, 128 or 320 bytes), which is public: the
contracts require `len = 32 d`. Every address and branch depends only on
the pointers and `len`.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- `mov d, #v` for a 64-bit constant: a `movz` and three `movk`s. -/
def movImm (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0, .movk .x d (v.extractLsb' 16 16) 1,
   .movk .x d (v.extractLsb' 32 16) 2, .movk .x d (v.extractLsb' 48 16) 3]

/-- A width: `c` coefficients of `d` bits per group of `nb` bytes. -/
structure Width where
  d : Nat
  c : Nat
  nb : Nat
  /-- The multiplier of `Compress_d`. -/
  mul : Nat

def width1 : Width := ⟨1, 8, 1, 315⟩
def width4 : Width := ⟨4, 2, 1, 2520⟩
def width10 : Width := ⟨10, 4, 5, 161271⟩

/-! ## `compressEncode` -/

/-- Coefficient `e` of the group, compressed, into its digit of `x9`. -/
def ceCoeff (w : Width) (e : Nat) : List Instr :=
  [.ldr .w .x10 .x0 (4 * e), .mul .x .x10 .x10 .x5, .add .x .x10 .x10 .x6, .lsr .x .x10 .x10 19,
    .logic .and .x .x10 .x10 .x7, .lsl .x .x10 .x10 (w.d * e), .add .x .x9 .x9 .x10]

/-- Byte `j` of `x9`. -/
def ceByte (j : Nat) : List Instr := [.lsr .x .x10 .x9 (8 * j), .strb .x10 .x2 j]

def ceBody (w : Width) : List Instr :=
  .movz .x .x9 0 0 :: (List.range w.c).flatMap (ceCoeff w) ++ (List.range w.nb).flatMap ceByte ++
    ([.addImm .x .x0 .x0 (4 * w.c), .addImm .x .x2 .x2 w.nb, .subImm .x .x11 .x11 1] : List Instr)

def ceLoop (w : Width) : Prog isa :=
  .seq (.block (movImm .x5 (BitVec.ofNat 64 w.mul) ++ movImm .x7 (BitVec.ofNat 64 (2 ^ w.d - 1)) ++
      movImm .x11 (BitVec.ofNat 64 (256 / w.c))))
    (.loop (.block (ceBody w)) (.nonzero .x .x11))

def compressEncode : Prog isa :=
  .seq (.block (movImm .x6 262080 ++ ([.subImm .x .x9 .x3 32] : List Instr))) <|
  .ite (.zero .x .x9) (ceLoop width1) <|
  .seq (.block [.subImm .x .x9 .x3 128]) <|
  .ite (.zero .x .x9) (ceLoop width4) (ceLoop width10)

/-! ## `decodeDecompress` -/

/-- Byte `j` of the group into `x9`. -/
def ddByte (j : Nat) : List Instr :=
  [.ldrb .x10 .x0 j, .lsl .x .x10 .x10 (8 * j), .add .x .x9 .x9 .x10]

/-- Digit `e` of `x9`, decompressed, to coefficient `e` of the group. -/
def ddCoeff (w : Width) (e : Nat) : List Instr :=
  [.lsr .x .x10 .x9 (w.d * e), .logic .and .x .x10 .x10 .x7, .mul .x .x10 .x10 .x5,
    .add .x .x10 .x10 .x6, .lsr .x .x10 .x10 w.d, .str .w .x10 .x3 (4 * e)]

def ddBody (w : Width) : List Instr :=
  .movz .x .x9 0 0 :: (List.range w.nb).flatMap ddByte ++ (List.range w.c).flatMap (ddCoeff w) ++
    ([.addImm .x .x0 .x0 w.nb, .addImm .x .x3 .x3 (4 * w.c), .subImm .x .x11 .x11 1] : List Instr)

def ddLoop (w : Width) : Prog isa :=
  .seq (.block (movImm .x6 (BitVec.ofNat 64 (2 ^ (w.d - 1))) ++
      movImm .x7 (BitVec.ofNat 64 (2 ^ w.d - 1)) ++ movImm .x11 (BitVec.ofNat 64 (256 / w.c))))
    (.loop (.block (ddBody w)) (.nonzero .x .x11))

def decodeDecompress : Prog isa :=
  .seq (.block (movImm .x5 3329 ++ ([.subImm .x .x9 .x1 32] : List Instr))) <|
  .ite (.zero .x .x9) (ddLoop width1) <|
  .seq (.block [.subImm .x .x9 .x1 128]) <|
  .ite (.zero .x .x9) (ddLoop width4) (ddLoop width10)

end VG.Impl.MlKem.AArch64

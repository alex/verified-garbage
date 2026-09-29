import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM-1024 on AArch64: compression with encoding, and decoding with decompression

`ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d` for the widths
`d` = 5 and 11 of ML-KEM-1024, by one loop over the 32 groups of 8
coefficients and `d` bytes. A group has `8d` bits, more than a register
holds for `d = 11`, so its bits stream through `x9`: it holds the bits
not yet stored (compression) or not yet decompressed (decompression), at
most `d + 7` of them.

* `compressEncode(f = x0, d = w1, out = x2, len = x3)`: for coefficient
  `e` of a group, `Compress_d(f[8g + e])` is added to `x9` above the bits
  it holds (`d e mod 8` of them), and every whole byte of `x9` is stored
  and shifted out (bytes `⌊d e / 8⌋` to `⌊d (e + 1) / 8⌋ - 1` of the
  group). `Compress_d(x)` is `((x · M_d + 261888) >> 19) mod 2ᵈ` (`M_d` in
  `x5`, 261888 in `x6`, `2ᵈ - 1` in `x7`).
* `decodeDecompress(b = x0, len = x1, d = w2, f = x3)`: for coefficient
  `e` of a group, the bytes it needs that are not yet in `x9` (bytes
  `⌈d e / 8⌉` to `⌈d (e + 1) / 8⌉ - 1` of the group) are added to `x9`
  above the bits it holds, and its low `d` bits are decompressed and
  shifted out: `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d` (`q` in `x5`,
  `2ᵈ⁻¹` in `x6`, `2ᵈ - 1` in `x7`).

The width is chosen by `len` (160 or 352 bytes), which is public: the
contracts require `len = 32 d`. Every address and branch depends only on
the pointers and `len`.
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64
open VG.Impl.MlKem.AArch64 (movImm)

/-- The multiplier of `Compress_d`. -/
def ceMul (d : Nat) : Nat := if d = 5 then 5040 else 322542

/-! ## `compressEncode` -/

/-- The bytes of a group stored before its coefficient `e`. -/
def ceJ (d e : Nat) : Nat := d * e / 8

/-- Coefficient `e` of the group, compressed, into `x9` above its `d e mod 8` bits. -/
def ceCoeff (d e : Nat) : List Instr :=
  [.ldr .w .x10 .x0 (4 * e), .mul .x .x10 .x10 .x5, .add .x .x10 .x10 .x6, .lsr .x .x10 .x10 19,
    .logic .and .x .x10 .x10 .x7, .lsl .x .x10 .x10 (d * e % 8), .add .x .x9 .x9 .x10]

/-- Byte `j` of the group: the low byte of `x9`, shifted out. -/
def ceByte (j : Nat) : List Instr := [.strb .x9 .x2 j, .lsr .x .x9 .x9 8]

/-- Coefficient `e`, and the bytes it completes. -/
def ceStep (d e : Nat) : List Instr :=
  ceCoeff d e ++ (List.range (ceJ d (e + 1) - ceJ d e)).flatMap fun k => ceByte (ceJ d e + k)

def ceBody (d : Nat) : List Instr :=
  .movz .x .x9 0 0 :: (List.range 8).flatMap (ceStep d) ++
    ([.addImm .x .x0 .x0 32, .addImm .x .x2 .x2 d, .subImm .x .x11 .x11 1] : List Instr)

def ceLoop (d : Nat) : Prog isa :=
  .seq (.block (movImm .x5 (BitVec.ofNat 64 (ceMul d)) ++ movImm .x7 (BitVec.ofNat 64 (2 ^ d - 1)) ++
      ([.movz .x .x11 32 0] : List Instr)))
    (.loop (.block (ceBody d)) (.nonzero .x .x11))

def compressEncode : Prog isa :=
  .seq (.block (movImm .x6 261888 ++ ([.subImm .x .x9 .x3 160] : List Instr))) <|
  .ite (.zero .x .x9) (ceLoop 5) (ceLoop 11)

/-! ## `decodeDecompress` -/

/-- The bytes of a group loaded before its coefficient `e`. -/
def ddJ (d e : Nat) : Nat := (d * e + 7) / 8

/-- Byte `j` of the group into `x9`, whose bits start at bit `d e` of the group. -/
def ddByte (d e j : Nat) : List Instr :=
  [.ldrb .x10 .x0 j, .lsl .x .x10 .x10 (8 * j - d * e), .add .x .x9 .x9 .x10]

/-- The low `d` bits of `x9`, decompressed, to coefficient `e` of the group, and shifted out. -/
def ddCoeff (d e : Nat) : List Instr :=
  [.logic .and .x .x10 .x9 .x7, .mul .x .x10 .x10 .x5, .add .x .x10 .x10 .x6, .lsr .x .x10 .x10 d,
    .str .w .x10 .x3 (4 * e), .lsr .x .x9 .x9 d]

/-- The bytes coefficient `e` needs, and the coefficient. -/
def ddStep (d e : Nat) : List Instr :=
  (List.range (ddJ d (e + 1) - ddJ d e)).flatMap (fun k => ddByte d e (ddJ d e + k)) ++ ddCoeff d e

def ddBody (d : Nat) : List Instr :=
  .movz .x .x9 0 0 :: (List.range 8).flatMap (ddStep d) ++
    ([.addImm .x .x0 .x0 d, .addImm .x .x3 .x3 32, .subImm .x .x11 .x11 1] : List Instr)

def ddLoop (d : Nat) : Prog isa :=
  .seq (.block (movImm .x6 (BitVec.ofNat 64 (2 ^ (d - 1))) ++ movImm .x7 (BitVec.ofNat 64 (2 ^ d - 1)) ++
      ([.movz .x .x11 32 0] : List Instr)))
    (.loop (.block (ddBody d)) (.nonzero .x .x11))

def decodeDecompress : Prog isa :=
  .seq (.block (movImm .x5 3329 ++ ([.subImm .x .x9 .x1 160] : List Instr))) <|
  .ite (.zero .x .x9) (ddLoop 5) (ddLoop 11)

end VG.Impl.MlKem1024.AArch64

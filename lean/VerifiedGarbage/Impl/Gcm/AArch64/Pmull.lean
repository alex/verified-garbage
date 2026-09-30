import VerifiedGarbage.TCB.AArch64.Isa

/-!
# GHASH with PMULL on AArch64

`vg_ghash_pmull(h = x0, y = x1, data = x2, n = x3, scratch = x4)`, with the
contract of `vg_ghash` (`Spec.Gcm.ghashContract`), for CPUs with FEAT_PMULL
(Rust's `aes` feature).

The arithmetic is that of `Impl.Gcm.X86_64.Pclmul`. A block is loaded with
`ldr q` and `rev64 .16b`, which leaves the first eight bytes of the block,
as a big-endian value, in the low doubleword and the last eight in the high
one: the halves of the block's value (the first byte the most significant)
swapped. In the bit-reflected representation of SP 800-38D:

* the carry-less product of a loaded block `a` and a block `t` (in the
  block's order), with `s` the halves of `t` swapped, is `x · a · t`, as 256
  bits `hi : mid : lo` (`hi` holding the low powers): `pmull a, s` and
  `pmull2 a, s` give `hi` and `lo`, and `pmull a, t` and `pmull2 a, t` the
  two halves of `mid`;
* the product is reduced into 128 bits as `hi ⊕ fold(mid ⊕ fold(lo))`, where
  `fold(r)`, the halves of `r` swapped (`ext #8`) plus the `pmull` of its low
  half by the constant `0xc2 · 2⁵⁶` (`x + x² + x⁷`, reflected), is of the
  class of `x⁶⁴ · r`, so that `mul(a, t) = x · a · t` in GF(2¹²⁸);
* to cancel the factor `x`, the hash subkey is used as `H' = H · x⁻¹ =
  mul(H, x⁻²)`, `x⁻²` a constant;
* `H'ᵏ = mul(H'ⁱ, H'ʲ) = Hᵏ · x⁻¹` (`i + j = k`) for `k = 2 … 8` are
  computed once per call when there are at least eight blocks, and kept in
  registers, as they are and with their halves swapped; eight blocks at a time
  `Y ← mul(Y ⊕ X₁, H'⁸) ⊕ mul(X₂, H'⁷) ⊕ … ⊕ mul(X₈, H')`, reducing the sum of
  the eight products once, and adding the product of `Y ⊕ X₁` last so that
  only it and the reduction wait for the previous `Y`; the remaining blocks go
  one at a time.
* `Y` is kept as loaded (its halves swapped), and stored with `rev64`.

Only caller-saved registers are used (`x5`–`x7`, `v0`–`v7`, `v16`–`v31`),
and `scratch` is not. Every branch and every address depends only on the
pointers and `n`.
-/

namespace VG.Impl.Gcm.AArch64.Pmull

open VG.AArch64

/-! Registers: `v0` `Y`, `v1` the reduction constant in both halves,
`v3`–`v5` the product (`lo`, `mid`, `hi`), `v6` a block, `v7` a
temporary, `v16`–`v23` `H'`–`H'⁸`, `v24`–`v31` the same with their halves
swapped. -/

abbrev Y : VReg := .v0
abbrev C : VReg := .v1
abbrev LO : VReg := .v3
abbrev MID : VReg := .v4
abbrev HI : VReg := .v5
abbrev A : VReg := .v6
abbrev T : VReg := .v7

/-- The register of `H'ᵏ`, `1 ≤ k ≤ 8`. -/
def tReg : Nat → VReg
  | 2 => .v17 | 3 => .v18 | 4 => .v19 | 5 => .v20 | 6 => .v21 | 7 => .v22 | 8 => .v23
  | _ => .v16

/-- The register of `H'ᵏ` with its halves swapped, `1 ≤ k ≤ 8`. -/
def sReg : Nat → VReg
  | 2 => .v25 | 3 => .v26 | 4 => .v27 | 5 => .v28 | 6 => .v29 | 7 => .v30 | 8 => .v31
  | _ => .v24

/-- The reduction constant `0xc2 · 2⁵⁶`. -/
def poly : BitVec 64 := 0xc200000000000000#64

/-- `x⁻²` (reflected): the high doubleword; the low one is 3. -/
def xInv2Hi : BitVec 64 := 0x4600000000000000#64

/-- Clear the product. -/
def zero : List Instr := [.vop (.movi0 LO), .vop (.movi0 MID), .vop (.movi0 HI)]

/-- Add the product of the loaded block `a` and the key `t` (`s` its halves swapped). -/
def acc (a s t : VReg) : List Instr :=
  [.vop (.pmull false T a s), .vop (.logic .eor HI HI T),
   .vop (.pmull true T a s), .vop (.logic .eor LO LO T),
   .vop (.pmull false T a t), .vop (.logic .eor MID MID T),
   .vop (.pmull true T a t), .vop (.logic .eor MID MID T)]

/-- `r ← swap(r) ⊕ pmull(r₀, 0xc2 · 2⁵⁶)`, of the class of `x⁶⁴ · r`. -/
def fold (r : VReg) : List Instr :=
  [.vop (.pmull false T r C), .vop (.ext r r r 8), .vop (.logic .eor r r T)]

/-- The product, reduced, into `d`: `hi ⊕ fold(mid ⊕ fold(lo))`. -/
def reduce (d : VReg) : List Instr :=
  fold LO ++ [.vop (.logic .eor MID MID LO)] ++ fold MID ++ [.vop (.logic .eor d HI MID)]

/-- `d ← mul(a, t)`, `a` as loaded, `s` the halves of `t` swapped. -/
def mul (d a s t : VReg) : List Instr := zero ++ acc a s t ++ reduce d

/-- The block at `[n, #off]` into `d`, as loaded. -/
def loadRev (d : VReg) (n : Reg) (off : Nat) : List Instr := [.ldrq d n off, .vop (.rev .rev64b d d)]

/-- Block `j` of the data into `v6`, as loaded. -/
def load (j : Nat) : List Instr := loadRev A .x2 (16 * j)

/-- `H'ᵏ = mul(H'ⁱ, H'ʲ)`, and its halves swapped. -/
def pow (k i j : Nat) : List Instr :=
  mul (tReg k) (sReg i) (sReg j) (tReg j) ++ [.vop (.ext (sReg k) (tReg k) (tReg k) 8)]

/-- The reduction constant in both halves of `v1`, and `x⁻²` in
`v17` and, its halves swapped, in `v25`. -/
def consts : List Instr :=
  [.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5),
   .movz .x .x6 3 0, .movz .x .x7 0x4600 3,
   .vop (.ins .d2 (tReg 2) 0 .x6), .vop (.ins .d2 (tReg 2) 1 .x7),
   .vop (.ins .d2 (sReg 2) 0 .x7), .vop (.ins .d2 (sReg 2) 1 .x6)]

/-- `H` (as loaded), the constants, `H' = mul(H, x⁻²)` and `Y`. -/
def prologue : List Instr :=
  loadRev A .x0 0 ++ consts ++ mul (tReg 1) A (sReg 2) (tReg 2) ++
  [.vop (.ext (sReg 1) (tReg 1) (tReg 1) 8)] ++ loadRev Y .x1 0 ++ [.lsr .x .x5 .x3 3]

/-- `H'²` to `H'⁸`. -/
def powers : List Instr :=
  pow 2 1 1 ++ pow 3 2 1 ++ pow 4 2 2 ++ pow 5 4 1 ++ pow 6 4 2 ++ pow 7 4 3 ++ pow 8 4 4

/-- Block `j + 1` of `k`, by `H'ᵏ⁻ʲ⁻¹`. -/
def blk (k j : Nat) : List Instr := load (j + 1) ++ acc A (sReg (k - 1 - j)) (tReg (k - 1 - j))

/-- Past `k` blocks: the pointer, the count, and the count of groups of eight. -/
def advance (k : Nat) : List Instr :=
  [.addImm .x .x2 .x2 (16 * k), .subImm .x .x3 .x3 k, .lsr .x .x5 .x3 3]

/-- `k` blocks (`k` = 1 or 8), then the pointer and the counts. The first
block, which `Y` is added to, goes last, so that only its products and the
reduction wait for the previous `Y`. -/
def body (k : Nat) : List Instr :=
  zero ++ (List.range (k - 1)).flatMap (blk k) ++ load 0 ++ [.vop (.logic .eor A A Y)] ++
  acc A (sReg k) (tReg k) ++ reduce Y ++ [.vop (.ext Y Y Y 8)] ++ advance k

def epilogue : List Instr := [.vop (.rev .rev64b Y Y), .strq Y .x1 0]

def ghash : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite (.zero .x .x5) (.block [])
        (.seq (.block powers) (.loop (.block (body 8)) (.nonzero .x .x5))))
      (.seq (.ite (.zero .x .x3) (.block []) (.loop (.block (body 1)) (.nonzero .x .x3)))
        (.block epilogue)))

end VG.Impl.Gcm.AArch64.Pmull

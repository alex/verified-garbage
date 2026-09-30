import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on AArch64: `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

`ntt(f = x0, scratch = x1)` and `nttInv(f = x0, scratch = x1)`: the
prologue stores a table of 256 zetas to `scratch` as `u32`s (`storeTab`):
`ζ^BitRev8(m) mod q` for `NTT`, and its negation `-ζ^BitRev8(m) mod q` for
`NTT⁻¹` (the `z` of Algorithm 42), then puts the constants of `reduce` in
`x9`–`x11`. Each of the eight layers runs its blocks, with `x2` pointing at
coefficient `j` of `f`, `x3` at the zeta of the block, `x4` counting the
blocks down and `x5` the butterflies of a block; the zeta of the block is
in `x6`.

* `NTT` (Algorithm 41): the layers with `len` = 128, 64, …, 1, whose zetas
  are consecutive, from `m = 1` up. A butterfly computes
  `t = ζ · f[j + len] mod q` (with `reduce`), and stores `f[j] - t`
  (`f[j] + q - t`, reduced with `csub`) to `f[j + len]` and `f[j] + t`
  (reduced) to `f[j]`.
* `NTT⁻¹` (Algorithm 42): the layers with `len` = 1, 2, …, 128, whose zetas
  are consecutive from `m = 255` down. A butterfly stores `f[j] + f[j + len]`
  (reduced) to `f[j]` and `z · (f[j] - f[j + len]) mod q` to `f[j + len]`.
  Then every coefficient is multiplied by `8347681 = 256⁻¹ mod q` and
  reduced.

A block ends with `x2` advanced past its upper half, so a layer ends with
`x2` at `f + 1024`, and moves it back. Every address and branch depends
only on the pointers.
-/

namespace VG.Impl.MlDsa.AArch64.Arith

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov csub)

/-- `ζ^BitRev8(m) mod q`. -/
def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

/-- `-ζ^BitRev8(m) mod q`. -/
def negZetaTab (m : Nat) : Nat := (8380417 - zetaTab m) % 8380417

/-- A butterfly of `NTT` on `[x2]` and `[x2 + 4len]`, with the zeta in `x6`. -/
def bfly (len : Nat) : List Instr :=
  [.ldr .w .x12 .x2 (4 * len), .mul .x .x12 .x12 .x6] ++ reduce .x12 .x13 ++
    [.ldr .w .x13 .x2 0, .add .x .x14 .x13 .x9, .sub .x .x14 .x14 .x12] ++ csub .x14 .x15 .x9 ++
    [.str .w .x14 .x2 (4 * len), .add .x .x13 .x13 .x12] ++ csub .x13 .x15 .x9 ++
    [.str .w .x13 .x2 0, .addImm .x .x2 .x2 4, .subImm .x .x5 .x5 1]

/-- A butterfly of `NTT⁻¹` on `[x2]` and `[x2 + 4len]`, with the zeta in `x6`. -/
def bflyInv (len : Nat) : List Instr :=
  [.ldr .w .x12 .x2 0, .ldr .w .x13 .x2 (4 * len), .add .x .x14 .x12 .x13] ++ csub .x14 .x15 .x9 ++
    [.str .w .x14 .x2 0, .add .x .x12 .x12 .x9, .sub .x .x12 .x12 .x13] ++ csub .x12 .x15 .x9 ++
    [.mul .x .x12 .x12 .x6] ++ reduce .x12 .x13 ++
    [.str .w .x12 .x2 (4 * len), .addImm .x .x2 .x2 4, .subImm .x .x5 .x5 1]

/-- A block of `len` butterflies `b`, with the zeta at `x3`, which then moves
by 4 bytes, up (`up`) or down. -/
def nttBlk (b : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block [.ldr .w .x6 .x3 0, if up then .addImm .x .x3 .x3 4 else .subImm .x .x3 .x3 4,
      .movz .x .x5 (BitVec.ofNat 16 len) 0])
    (.seq (.loop (.block b) (.nonzero .x .x5))
      (.block [.addImm .x .x2 .x2 (4 * len), .subImm .x .x4 .x4 1]))

/-- A layer: its `128 / len` blocks, then `x2` back to `f`. -/
def nttLay (b : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block [.movz .x .x4 (BitVec.ofNat 16 (128 / len)) 0])
    (.seq (.loop (nttBlk b len up) (.nonzero .x .x4)) (.block [.subImm .x .x2 .x2 1024]))

/-- The layers of `NTT` with `len` in `lens`. -/
def nttLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bfly len) len true) (nttLays lens)

/-- The layers of `NTT⁻¹` with `len` in `lens`. -/
def nttInvLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bflyInv len) len false) (nttInvLays lens)

/-- The table `t` to `scratch`, the constants, `x2` = `f` and `x3` at entry
`k` of the table. -/
def nttPro (t : Nat → Nat) (k : Nat) : List Instr :=
  storeTab t 256 .x1 ++ consts ++ [mov .x2 .x0, .addImm .x .x3 .x1 (4 * k)]

def ntt : Prog isa := .seq (.block (nttPro zetaTab 1)) (nttLays [128, 64, 32, 16, 8, 4, 2, 1])

/-- A coefficient times `8347681` (in `x6`), reduced. -/
def scaleBody : List Instr :=
  [.ldr .w .x12 .x2 0, .mul .x .x12 .x12 .x6] ++ reduce .x12 .x13 ++
    [.str .w .x12 .x2 0, .addImm .x .x2 .x2 4, .subImm .x .x5 .x5 1]

def nttInv : Prog isa :=
  .seq (.block (nttPro negZetaTab 255))
    (.seq (nttInvLays [1, 2, 4, 8, 16, 32, 64, 128])
      (.seq (.block (movW .x6 (BitVec.ofNat 32 8347681) ++ [.movz .x .x5 256 0]))
        (.loop (.block scaleBody) (.nonzero .x .x5))))

end VG.Impl.MlDsa.AArch64.Arith

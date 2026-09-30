import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

`ntt(f = r0, scratch = r1)` and `nttInv(f = r0, scratch = r1)` save
`r4`–`r10` (`saving`: 28 bytes of stack) and store a table of 256 zetas to
`scratch` as `u32`s (`storeTab`, through `r12`): `ζ^BitRev8(m) mod q` for
`NTT`, and its negation `-ζ^BitRev8(m) mod q` for `NTT⁻¹` (the `z` of
Algorithm 42). With `q` in `r4`, each of the eight layers runs its blocks,
with `r0` pointing at coefficient `j` of `f`, `r1` at the zeta of the block,
`r2` counting the blocks down and `r3` the butterflies of a block; a block
puts the pieces of its zeta in `r5`–`r7` (`zPieces`), for `mulz`. The layers
are separate code, each with its `len` in the offsets of its loads and
stores.

* `NTT` (Algorithm 41): the layers with `len` = 128, 64, …, 1, whose zetas
  are consecutive, from `m = 1` up. A butterfly computes
  `t = ζ · f[j + len] mod q` (`mulz`, then `csub`), and stores `f[j] - t`
  (reduced with `fixup`) to `f[j + len]` and `f[j] + t` (reduced with
  `csub`) to `f[j]`.
* `NTT⁻¹` (Algorithm 42): the layers with `len` = 1, 2, …, 128, whose zetas
  are consecutive from `m = 255` down. A butterfly stores `f[j] + f[j + len]`
  (reduced) to `f[j]` and `z · (f[j] - f[j + len]) mod q` to `f[j + len]`.
  Then every coefficient is multiplied by `8347681 = 256⁻¹ mod q`, whose
  pieces are 509, 64 and 33, and reduced.

A block ends with `r0` advanced past its upper half, so a layer ends with
`r0` at `f + 1024`, and moves it back. Every address and branch depends
only on the pointers.
-/

namespace VG.Impl.MlDsa.Arm.Arith

open VG.Arm

/-- `ζ^BitRev8(m) mod q`. -/
def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

/-- `-ζ^BitRev8(m) mod q`. -/
def negZetaTab (m : Nat) : Nat := (8380417 - zetaTab m) % 8380417

/-- `t i` to `[r1 + 4i]`, through `r12`. -/
def tabStep (t : Nat → Nat) (i : Nat) : List Instr :=
  [.movw .r12 (BitVec.ofNat 16 (t i % 65536)), .movt .r12 (BitVec.ofNat 16 (t i / 65536)),
   .str .r12 .r1 (4 * i)]

/-- The table `t 0, …, t (n - 1)` at `r1`. -/
def storeTab (t : Nat → Nat) (n : Nat) : List Instr := (List.range n).flatMap (tabStep t)

/-- The registers the transforms save. -/
def nttSaved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- A butterfly of `NTT` on `[r0]` and `[r0 + 4len]`, with the pieces of the
zeta in `r5`–`r7`. -/
def bfly (len : Nat) : List Instr :=
  [.ldr .r8 .r0 (4 * len)] ++ mulz .r9 .r8 .r12 ++ csub .r9 .r12 .r4 ++
    [.ldr .r8 .r0 0, .dp .sub .r10 .r8 (.reg .r9)] ++ fixup .r10 .r12 .r4 ++
    [.str .r10 .r0 (4 * len), .dp .add .r8 .r8 (.reg .r9)] ++ csub .r8 .r12 .r4 ++
    [.str .r8 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

/-- A butterfly of `NTT⁻¹` on `[r0]` and `[r0 + 4len]`, with the pieces of the
zeta in `r5`–`r7`. -/
def bflyInv (len : Nat) : List Instr :=
  [.ldr .r8 .r0 0, .ldr .r9 .r0 (4 * len), .dp .add .r10 .r8 (.reg .r9)] ++ csub .r10 .r12 .r4 ++
    [.str .r10 .r0 0, .dp .sub .r8 .r8 (.reg .r9)] ++ fixup .r8 .r12 .r4 ++ mulz .r9 .r8 .r12 ++
    csub .r9 .r12 .r4 ++ [.str .r9 .r0 (4 * len), .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

/-- A block of `len` butterflies `b`: the pieces of its zeta, at `r1`, which
then moves by 4 bytes (`op` is `add` or `sub`). -/
def nttBlk (b : List Instr) (len : Nat) (op : DpOp) : Prog isa :=
  .seq (.block ([.ldr .r8 .r1 0] ++ zPieces .r8 ++
      [.dp op .r1 .r1 (.imm 4), .mov .r3 (.imm (BitVec.ofNat 32 len))]))
    (.seq (.loop (.block b) .ne)
      (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * len))), .subs .r2 .r2 (.imm 1)]))

/-- A layer: its `128 / len` blocks, then `r0` back to `f`. -/
def nttLay (b : List Instr) (len : Nat) (op : DpOp) : Prog isa :=
  .seq (.block [.mov .r2 (.imm (BitVec.ofNat 32 (128 / len)))])
    (.seq (.loop (nttBlk b len op) .ne) (.block [.dp .sub .r0 .r0 (.imm 1024)]))

/-- The layers of `NTT` with `len` in `lens`. -/
def nttLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bfly len) len .add) (nttLays lens)

/-- The layers of `NTT⁻¹` with `len` in `lens`. -/
def nttInvLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bflyInv len) len .sub) (nttInvLays lens)

def ntt : Prog isa :=
  saving nttSaved (.seq (.block (storeTab zetaTab 256 ++ loadQ .r4 ++ [.dp .add .r1 .r1 (.imm 4)]))
    (nttLays [128, 64, 32, 16, 8, 4, 2, 1]))

/-- A coefficient times `8347681`, reduced. -/
def scaleBody : List Instr :=
  [.ldr .r8 .r0 0] ++ mulz .r9 .r8 .r12 ++ csub .r9 .r12 .r4 ++
    [.str .r9 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

def nttInv : Prog isa :=
  saving nttSaved (.seq (.block (storeTab negZetaTab 256 ++ loadQ .r4 ++ [.dp .add .r1 .r1 (.imm 1020)]))
    (.seq (nttInvLays [1, 2, 4, 8, 16, 32, 64, 128])
      (.seq (.block [.movw .r5 509, .movw .r6 64, .movw .r7 33, .mov .r3 (.imm 256)])
        (.loop (.block scaleBody) .ne))))

end VG.Impl.MlDsa.Arm.Arith

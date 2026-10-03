import VerifiedGarbage.Proof.MlKem.X86_64.S4Scalar
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import VerifiedGarbage.Proof.MlKem.X86_64.Prfs

/-!
# Implementations of `vg_mlkem_sample_ntt4` on x86-64

A `Sample4Impl` is what a function that calls `vg_mlkem_sample_ntt4` needs
of it, so that its proof holds for every implementation: each is a variant
of the interface `MlKemSample4` on x86-64 (`Variants/MlKemSample4/X86_64/`),
and each caller (the top-level functions of ML-KEM-768 and ML-KEM-1024, in
`Generic/MlKemSample4/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Both implementations use 24 bytes of stack below their
return address (`vg_mlkem_sample_ntt`'s calls, three deep).

Each also comes with the computation of several outputs of `PRF₂` that its
callers inline (`Callee4.prfs`): one at a time for the baseline, and four
at a time with AVX2 for `vg_mlkem_sample_ntt4_avx2` (`Prfs.lean`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- An implementation of `vg_mlkem_sample_ntt4` on x86-64. -/
structure Sample4Impl where
  /-- Its symbol and code. -/
  callee : Impl.MlKem.X86_64.Callee4
  /-- It is correct. -/
  ok : ∀ s, sample4K.pre s → ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ sample4K.post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa sample4K.pre sample4K.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- Its calls are at most three deep. -/
  depth_le : callee.code.depth ≤ 3
  /-- It keeps MXCSR's control bits. -/
  mxcsr : ctlOk callee.code = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- Its outputs of `PRF₂` are correct. -/
  prfs_ok : ∀ {rbs wbs : List (Reg × Nat)} {s : State}, Lay rbs wbs s → (∀ b ∈ rbs ++ wbs, b.1 ∈ bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → prfsChk (rbs ++ wbs) wbs n o wl = true →
      WP isa (callee.prfs N₀ n o wl) s (PrfsPost s N₀ n o wl)
  /-- They are constant time. -/
  prfs_tr : ∀ {rbs wbs : List (Reg × Nat)}, (∀ b ∈ rbs ++ wbs, b.1 ∈ bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → prfsChk (rbs ++ wbs) wbs n o wl = true →
      RelCT isa (LRel rbs wbs) (callee.prfs N₀ n o wl) fun _ _ => True
  prfs_ctl : ∀ N₀ n o wl, ctlOk (callee.prfs N₀ n o wl) = true
  prfs_sp : ∀ N₀ n o wl, (callee.prfs N₀ n o wl).all (fun i => !isa.writesSp i) = true
  /-- The polynomial arithmetic that goes with it is correct, constant
  time, and safe to call. -/
  arith : ArithOk callee.arith
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- How its callers compute the outputs of `PRF₂`, for their documentation. -/
  prfsDoc : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Sample4Impl

/-- The baseline implementation, `vg_mlkem_sample_ntt4`, which calls `vg_mlkem_sample_ntt`. -/
def scalar : Sample4Impl where
  callee := .scalar
  ok := S4.correct_scalar
  ct := S4.ct_scalar
  nosp := nosp_of (by decide +kernel)
  depth_le := by decide +kernel
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  prfs_ok := fun L hcs => prfsScalar_ok L hcs
  prfs_tr := fun hcs => prfsScalar_tr hcs
  prfs_ctl := prfsScalar_ctl
  prfs_sp := prfsScalar_sp
  arith := ArithOk.sse
  suffix := ""
  prfsDoc := "one at a time"
  features := []

/-- The AVX2 implementation, `vg_mlkem_sample_ntt4_avx2`. -/
def avx2 : Sample4Impl where
  callee := .avx2
  ok := S4.correct
  ct := S4.ct
  nosp := nosp_of (by decide +kernel)
  depth_le := by decide +kernel
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  prfs_ok := fun L hcs => prfsAvx2_ok L hcs
  prfs_tr := fun hcs => prfsAvx2_tr hcs
  prfs_ctl := prfsAvx2_ctl
  prfs_sp := prfsAvx2_sp
  arith := ArithOk.avx2
  suffix := "_avx2"
  prfsDoc := "four at a time, with AVX2 (and the first one or two of `4k + 1` or `4k + 2` on their own)"
  features := ["avx", "avx2"]

end Sample4Impl

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v`: the kernel evaluates only
code that does not call the implementation `v`, each part once (rather than
failing on code that does, after evaluating its other parts). -/
elab "closed_in " v:ident : tactic => withMainContext do
  let e ← elabTerm v none
  if (← instantiateMVars (← getMainTarget)).containsFVar e.fvarId! then
    throwError "the goal mentions {e}"

/-- `ctlOk` of code that calls the implementation `v`: evaluated by the
kernel but for the calls of `v`. -/
macro "s4_ctl " v:ident : tactic =>
  `(tactic| repeat' (first | (closed_in $v; decide +kernel) | apply ctlOk_seq | apply ctlOk_ite |
    (apply ctlOk_call; exact ($v).mxcsr) | exact ($v).prfs_ctl _ _ _ _ | exact ($v).arith.mul.ctl |
    exact ($v).arith.ntt.ctl | exact ($v).arith.nttInv.ctl | rfl))

/-- Code that does not call the implementation `v` never writes the stack pointer: by evaluation. -/
macro "s4_sp_closed " v:ident : tactic =>
  `(tactic| (closed_in $v; exact Code.all_of_allInstrs (by decide +kernel)))

/-- That code that calls the implementation `v` never writes the stack pointer. -/
macro "s4_sp " v:ident : tactic =>
  `(tactic| repeat' (first | s4_sp_closed $v | apply all_seq | apply all_ite | (apply all_call; exact ($v).spSafe) |
    exact ($v).prfs_sp _ _ _ _ | exact ($v).arith.mul.sp | exact ($v).arith.ntt.sp | exact ($v).arith.nttInv.sp | rfl))

end VG.Proof.MlKem.X86_64

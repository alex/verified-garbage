import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import VerifiedGarbage.Proof.X448.AArch64.Fast.StepOps

/-!
# X448 on AArch64: interleaved code

Untrusted: everything here is checked by Lean. `weave a b` is a merge of
`a` and `b`, so for independent blocks it runs as `a` and then `b`.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64 VG.AArch64.Interleave
open VG.Impl.X448.AArch64.Fast (weave weaveGo codeOf ops)

theorem weaveGo_merge (n m : Nat) : ∀ f i j (a b : List Instr), Merge (weaveGo n m f i j a b) a b
  | 0, _, _, a, b => Merge.append a b
  | _ + 1, _, _, [], b => Merge.nil_left b
  | _ + 1, _, _, x :: a, [] => Merge.nil_right (x :: a)
  | f + 1, i, j, x :: a, y :: b => by
    rw [weaveGo]
    split
    · exact .left (weaveGo_merge n m f _ _ _ _)
    · exact .right (weaveGo_merge n m f _ _ _ _)

theorem weave_merge (a b : List Instr) : Merge (weave a b) a b := weaveGo_merge _ _ _ _ _ _ _

/-- Independent blocks, interleaved, run as the first and then the second. -/
theorem WP.weave {a b : List Instr}
    (hind : ((blockFp a).bind fun A => (blockFp b).map fun B => A.indep B) = some true) {s : State}
    {Q : State → Prop} (h : WP isa (.block a) s fun t => WP isa (.block b) t Q) : WP isa (.block (weave a b)) s Q :=
  WP.merge (weave_merge a b) (indeps_of_check hind) (WP.block_append_iff.mpr h)

theorem block_codeOf {l : List Impl.X448.AArch64.Fast.Op} {s : State} {Q : State → Prop}
    (h : WP isa (ops l) s Q) : WP isa (.block (codeOf l)) s Q := by
  induction l generalizing s with
  | nil => exact h
  | cons o os ih =>
    rw [ops, WP.seq_iff] at h
    exact WP.block_append_iff.mpr (WP.mono h fun t ht => ih ht)

end VG.Proof.X448.AArch64.Fast

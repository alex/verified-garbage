import VerifiedGarbage.Proof.Framework.Block

/-!
# Straight-line code built from indexed steps
-/

namespace VG

variable {M : ISA}

/-- Running `f 0 ++ f 1 ++ … ++ f (n - 1)` by induction, with an invariant indexed by the step. -/
theorem wp_range_flatMap {f : Nat → List M.Instr} {N : Nat} (Inv : Nat → M.State → Prop)
    (hstep : ∀ k s, k < N → Inv k s → WP M (.block (f k)) s (Inv (k + 1))) :
    ∀ n ≤ N, ∀ s, Inv 0 s → WP M (.block ((List.range n).flatMap f)) s (Inv n) := by
  intro n hn
  induction n with
  | zero => intro s hs; exact WP.block_nil hs
  | succ n ih =>
    intro s hs
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega) s hs) fun s' h => hstep n s' (by omega) h

end VG

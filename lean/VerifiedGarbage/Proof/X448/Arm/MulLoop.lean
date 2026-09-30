import VerifiedGarbage.Proof.X448.Arm.Init
import VerifiedGarbage.Proof.X448.Arm.Row

/-!
# X448 on ARMv7: the multiplication loop

Untrusted: everything here is checked by Lean. All 28 rows terminate at a
public counter, producing 56 bounded product limbs.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

theorem mulLoop_ok {b : BitVec 32} {x y : Nat} (hx : Slot x) (hy : Slot y)
    {s0 s : State} (hlx : Bounded s0.mem (State.addr b) x) (hly : Bounded s0.mem (State.addr b) y)
    (hs : RowInv b x y s0 0 s) :
    WP isa (.loop (.block (row x y)) .ne) s (RowInv b x y s0 28) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ i, n = 28 - i ∧ i < 28 ∧ RowInv b x y s0 i s') ?_ 28 s ⟨0, rfl, by decide, hs⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok hx hy hlx hly hi hr) fun t ⟨ht, hz⟩ => ?_
  by_cases h28 : i + 1 = 28
  · refine .inl ⟨by rw [eval_ne, hz]; simp only [h28, decide_true, Bool.not_true], ?_⟩
    rw [h28] at ht
    exact ht
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega,
      28 - (i + 1), by omega, i + 1, rfl, by omega, ht⟩

end VG.Proof.X448.Arm

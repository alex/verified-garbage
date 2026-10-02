import VerifiedGarbage.Proof.X448.X86.Init
import VerifiedGarbage.Proof.X448.X86.Row

/-!
# X448 on x86 (32-bit): the multiplication loop

All 28 rows terminate at a public counter, producing 56 bounded product limbs.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem mulLoop_ok {base : Addr} {x y : Nat} (hx : Slot x) (hy : Slot y)
    {s0 s : State} (hlx : Bounded s0.mem base x) (hly : Bounded s0.mem base y)
    (hs : RowInv base x y s0 0 s) :
    WP isa (.loop (.block (row x y)) .ne) s (RowInv base x y s0 28) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ i, n = 28 - i ∧ i < 28 ∧ RowInv base x y s0 i s') ?_ 28 s ⟨0, rfl, by decide, hs⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok hx hy hlx hly hi hr) fun t ⟨ht, hz⟩ => ?_
  by_cases h28 : i + 1 = 28
  · refine .inl ⟨by simp only [eval, hz, h28, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rw [h28] at ht
    exact ht
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false h28, Option.map_some, Bool.not_false],
      28 - (i + 1), by omega, i + 1, rfl, by omega, ht⟩

end VG.Proof.X448.X86

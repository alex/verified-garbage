import VerifiedGarbage.Proof.X448.X86_64.Iter

/-!
# X448 on x86-64: all 448 ladder iterations

Untrusted: everything here is checked by Lean. A decreasing public counter
connects the loop to the specification's descending fold over scalar bits.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → LInv base k u s₀ s n →
      WP isa (.loop step .ne) s fun s' => LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := step) (c := .ne)
    (Q := fun s' => LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (step_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : ∀ s', s'.gpr .rbx = BitVec.ofNat 64 448 → (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → LInv base k u s₀ s' 448) :
    WP isa ladder s fun s' => LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 448)]) s (fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 448 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s' ⟨h1, h2, h3, h4, h5⟩ => loop_ok hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

end VG.Proof.X448.X86_64

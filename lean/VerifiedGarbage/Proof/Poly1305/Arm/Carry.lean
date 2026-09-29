import VerifiedGarbage.Proof.Poly1305.Arm.Words

/-!
# Poly1305 on 32-bit ARM: carrying and the final reduction

Untrusted: everything here is checked by Lean. The columns (or limbs) are in
`r3`–`r11` and `r1` (`Cols`); `carryStep` moves a column's bits from 13 up
to the next column (`carries_ok`), `carryFold` carries them all into `fold`
(`carryFold_ok`), and `reduce` reduces them fully (`reduceRegs_ok`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- The columns (or limbs) are `v`, in `r3`–`r11` and `r1`. -/
def Cols (v : Nat → Nat) (s : State) : Prop := ∀ j < 10, (s.gpr (yr j)).toNat = v j

/-- The mask `movw r2, #0x1fff` leaves in `r2`. -/
abbrev maskV : BitVec 32 := (0x1fff#16).setWidth 32

/-- The registers of the columns. -/
def cregs : List Reg := .r1 :: yregs

theorem yr_cregs : ∀ k < 10, yr k ∈ cregs := by decide

theorem cregs_r2 : Reg.r2 ∉ cregs := by decide
theorem cregs_r12 : Reg.r12 ∉ cregs := by decide
theorem cregs_r0 : Reg.r0 ∉ cregs := by decide

theorem carryStep_ok {k : Nat} (hk : k < 9) {s : State} (hm : s.gpr .r2 = maskV)
    (hb : (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 < 2 ^ 32) :
    WP isa (.block (carryStep k)) s fun s' =>
      (s'.gpr (yr (k + 1))).toNat = (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 ∧
      (s'.gpr (yr k)).toNat = (s.gpr (yr k)).toNat % 2 ^ 13 ∧ Keeps [yr k, yr (k + 1)] s s' := by
  have hne : yr k ≠ yr (k + 1) := fun h => absurd (yr_inj _ (by omega) _ (by omega) h) (by omega)
  have h2 : yr k ≠ .r2 := (yr_ne k hk).2.2.1
  refine wp_add (op2_lsr (by omega)) fun s1 u1 => wp_and (op2_reg _ _) fun s2 u2 => WP.block_nil ?_
  refine ⟨?_, ?_, (u1.keeps (by simp)).trans (u2.keeps (by simp))⟩
  · rw [u2.other _ hne.symm, u1.gpr, toNat_add_lt (by rw [toNat_shr]; exact hb), toNat_shr]
  · rw [u2.gpr, u1.other _ hne, u1.other _ (Ne.symm (yr_ne' (k + 1) (by omega)).2.1), hm, toNat_and_mask]

/-- After the carries from columns `a`, …, `a + k - 1`. -/
structure CI (f : Nat → Nat) (a : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  cols : Cols (carryN f a k) s
  keeps : Keeps cregs s₀ s

theorem carries_ok (a n : Nat) (hn : n + a ≤ 9) {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19)
    {s : State} (hc : Cols f s) (hm : s.gpr .r2 = maskV) :
    WP isa (.block ((List.range n).flatMap fun k => carryStep (k + a))) s fun s' =>
      Cols (carryN f a n) s' ∧ Keeps cregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (CI f a s) (fun k s' hk h => ?_) n (Nat.le_refl _) s
    ⟨hc, Keeps.refl _ _⟩) fun s' h => ⟨h.cols, h.keeps⟩
  have hm' : s'.gpr .r2 = maskV := by rw [h.keeps.gpr _ cregs_r2, hm]
  have hb := carryN_step_lt f a hf k (by omega)
  refine WP.mono (carryStep_ok (k := k + a) (by omega) hm' (by
    rw [h.cols _ (by omega), h.cols _ (by omega)]; exact hb)) fun s'' ⟨e1, e0, hk⟩ => ⟨?_, ?_⟩
  · intro j hj
    simp only [carryN, cstep]
    by_cases ej : j = k + a
    · subst ej; rw [iteT rfl, e0, h.cols _ hj]
    by_cases ej' : j = k + a + 1
    · subst ej'; rw [iteF ej, iteT rfl, e1, h.cols _ hj, h.cols _ (by omega)]
    · rw [iteF ej, iteF ej', hk.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => ej (yr_inj _ hj _ (by omega) e), fun e => ej' (yr_inj _ hj _ (by omega) e)⟩),
        h.cols _ hj]
  · exact h.keeps.trans (hk.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact yr_cregs _ (by omega))

end VG.Proof.Poly1305.Arm

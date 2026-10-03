import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

def columnRegs (x : Nat) : List VReg := (List.range 5).map fun y => vreg (x+5*y)

/-- Apply a theta correction to the five words in one column. -/
theorem column_ok (x : Nat) (hx : x < 5) (s : State) :
    WP isa (.block ((List.range 5).map fun y =>
      .vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30))) s fun s' =>
      VChg (columnRegs x) s s' ∧ s'.v .v30 = s.v .v30 ∧
      ∀ i < 25, s'.v (vreg i) = if i%5 = x then s.v (vreg i) ^^^ s.v .v30 else s.v (vreg i) := by
  have h30 (y : Nat) (hy : y < 5) : VReg.v30 ≠ vreg (x+5*y) := by
    change vreg 30 ≠ vreg (x+5*y)
    rw [ne_eq,vreg_inj 30 (by decide) (x+5*y) (by omega)]; omega
  have hm : ∀ y < 5, vreg (x+5*y) ∈ columnRegs x := by
    intro y hy
    exact List.mem_map.mpr ⟨y,List.mem_range.mpr hy,rfl⟩
  have heq : ∀ i < 25, ∀ y < 5, i = x+5*y ↔ i%5 = x ∧ i/5 = y := by
    intro i hi y hy
    omega
  have hcode : (List.range 5).map (fun y =>
      Instr.vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30)) =
      (List.range 5).flatMap (fun y => [Instr.vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30)]) := by
    rfl
  rw [hcode]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg (columnRegs x) s s' ∧ s'.v .v30 = s.v .v30 ∧
      ∀ i < 25, s'.v (vreg i) =
        if i%5 = x ∧ i/5 < k then s.v (vreg i) ^^^ s.v .v30 else s.v (vreg i))
    (fun y s' hy ⟨hchg,hv30,hvals⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,rfl,by intro i hi; rw [ite_eq_right (by omega)]⟩)
    fun s' ⟨hchg,hv30,hvals⟩ => ⟨hchg,hv30,fun i hi => by
      rw [hvals i hi]
      have hdiv : i/5 < 5 := by omega
      simp only [hdiv,and_true]⟩
  refine wp_vop (d := vreg (x+5*y)) rfl fun s'' h => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact (hchg.trans h.chg).mono (by
      intro r hr
      rw [List.mem_append,List.mem_singleton] at hr
      rcases hr with hh | rfl
      · exact hh
      · exact hm y hy)
  · rw [h.get .v30 (h30 y hy),hv30]
  · intro i hi
    by_cases hid : i = x+5*y
    · subst i
      rw [h.v,hvals _ (by omega),hv30,ite_eq_right (by
        have := (heq (x+5*y) (by omega) y hy).mp rfl; omega),ite_eq_left (by
        have := (heq (x+5*y) (by omega) y hy).mp rfl; omega)]
    · rw [h.get (vreg i) (by rw [ne_eq,vreg_inj i (by omega) (x+5*y) (by omega)]; exact hid),hvals i hi]
      have hi' : ¬ (i%5 = x ∧ i/5 = y) := by rw [← heq i hi y hy]; exact hid
      by_cases hc : i%5 = x ∧ i/5 < y <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
end VG.Proof.Sha3.AArch64.Neon

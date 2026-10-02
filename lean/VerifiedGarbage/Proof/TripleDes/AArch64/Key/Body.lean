import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Composition

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Rc2.AArch64 (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.subImm .x .x4 .x1 16] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (s.gpr .x1 == 16) ∧ Keep [.x4] s s' := by
  refine ⟨s.write .x .x4 (s.gpr .x1 - 16), ?_, ?_, write_keep _ _⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show (16 : Nat) < 4096 from by decide, ite_true, State.read, BitVec.setWidth_eq]
    rfl
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [.x4] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.AArch64.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.AArch64.Key.component 0 0)
      (.seq (Impl.TripleDes.AArch64.Key.component 8 1)
        (.seq (.block [.subImm .x .x4 .x1 16])
          (.seq (.ite (.zero .x .x4) (.block Impl.TripleDes.AArch64.Key.copyThird)
            (Impl.TripleDes.AArch64.Key.component 16 2)) (.block Impl.TripleDes.AArch64.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (Components origin · 3)) ?_
  · intro t ht
    exact finish t ht
  have flag : isa.eval (.zero .x .x4) s₃ = some (decide ((origin.gpr .x1).toNat = 16)) := by
    rw [flag₃, hs₂.reg .x1 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .x1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.AArch64.Key

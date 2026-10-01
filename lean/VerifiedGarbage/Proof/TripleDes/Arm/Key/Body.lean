import VerifiedGarbage.Proof.TripleDes.Arm.Key.Composition

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Arm.RegUpd
open VG.Proof.Rc2.Arm (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.cmp .r1 (.imm 16)] s = some s' ∧
      isa.eval .eq s' = some (s.gpr .r1 == 16) ∧ Keep [.r4] s s' := by
  refine ⟨subFlags s (s.gpr .r1) 16, ?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, ite_true, Option.map_some]
  · change some (s.gpr .r1 - 16 == 0) = _
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [.r4] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 32) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.Arm.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.Arm.Key.component 0 0)
      (.seq (Impl.TripleDes.Arm.Key.component 8 1)
        (.seq (.block [.cmp .r1 (.imm 16)])
          (.seq (.ite .eq (.block Impl.TripleDes.Arm.Key.copyThird)
            (Impl.TripleDes.Arm.Key.component 16 2)) (.block Impl.TripleDes.Arm.Key.restore))))) s Q := by
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
  have flag : isa.eval .eq s₃ = some (decide ((origin.gpr .r1).toNat = 16)) := by
    rw [flag₃, hs₂.reg .r1 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .r1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.Arm.Key

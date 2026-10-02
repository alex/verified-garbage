import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Composition

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Rc2.X86_64 (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rsi (.imm 16)] s = some s' ∧
      s'.zf = some (s.gpr .rsi == 16) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_, ?_⟩
  · rw [zf_arithFlags]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      change (s.gpr .rsi - (16 : BitVec 64) = (0 : BitVec 64)) ↔ s.gpr .rsi = (16 : BitVec 64)
      bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by simp)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

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
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.X86_64.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86_64.Key.component 0 0)
      (.seq (Impl.TripleDes.X86_64.Key.component 8 1)
        (.seq (.block [.alu .cmp .rsi (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86_64.Key.copyThird)
            (Impl.TripleDes.X86_64.Key.component 16 2)) (.block Impl.TripleDes.X86_64.Key.restore))))) s Q := by
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
  have flag : s₃.zf = some (decide ((origin.gpr .rsi).toNat = 16)) := by
    rw [flag₃, hs₂.reg .rsi (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .rsi).toNat = 16
  · apply WP.ite true (by simp only [eval, flag, h16, decide_true])
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simp only [eval, flag, h16, decide_false])
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86_64.Key

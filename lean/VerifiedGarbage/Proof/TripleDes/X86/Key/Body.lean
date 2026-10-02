import VerifiedGarbage.Proof.TripleDes.X86.Key.Composition

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem lengthCompare (x : BitVec 32) : ((x - 16) == 0) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h' : x = 16 := by bv_omega_using [h]
    rw [h']; rfl
  · intro h
    have h' : x = 16 := BitVec.eq_of_toNat_eq h
    rw [h']; rfl

theorem cmpLength_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)] s = some s' ∧
      isa.eval .e s' = some (decide (keyLength s = 16)) ∧ Keep [.eax] s s' := by
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load32, State.ea, memOp, hr, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, ite_true]
    rfl, ?_, ?_⟩
  · change some ((s.mem.readW (wordAddr (s.gpr .esp) 2) 32 - 16) == 0) = _
    rw [← argument_word s 1]
    exact congrArg some (lengthCompare (arg s 1))
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [.eax] s t) : Components origin t n := by
  have sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide)
  refine ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide)).trans hs.bp, sp.trans hs.sp, ?_, ?_⟩
  · intro i hi
    unfold arg argAddr
    rw [sp, ht.mem]
    exact hs.args i hi
  · rw [ht.mem]; exact hs.frame

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (lenRead : InRegions (origin.rd ++ origin.wr) (wordAddr (origin.gpr .esp) 2) 4)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.X86.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86.Key.component 0 0)
      (.seq (Impl.TripleDes.X86.Key.component 8 1)
        (.seq (.block [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86.Key.copyThird)
            (Impl.TripleDes.X86.Key.component 16 2)) (.block Impl.TripleDes.X86.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
    (by rw [hs₂.rd, hs₂.wr, hs₂.sp]; exact lenRead)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (Components origin · 3)) ?_
  · intro t ht; exact finish t ht
  have flag : isa.eval .e s₃ = some (decide (keyLength origin = 16)) := by
    rw [flag₃, keyLength, hs₂.args 1 (by decide)]
    rfl
  by_cases h16 : keyLength origin = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThirdStep_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86.Key

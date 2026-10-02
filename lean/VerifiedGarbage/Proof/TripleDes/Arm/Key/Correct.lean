import VerifiedGarbage.Proof.TripleDes.Arm.Key.Contract

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.Arm.Key.expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, valid, keyFit, outputFit, scratchFit⟩ := hs
  have scratchWrites : ∀ i < 9, InRegions s.wr ((State.addr (s.gpr .r3)) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨(State.addr (s.gpr .r3)), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.Arm.Key.expandKey]
  apply WP.seq
  apply WP.mono (save_ok s (by omega_using [scratchFit]) scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨(State.addr (s.gpr .r0)), (s.gpr .r1).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .r1)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨(State.addr (s.gpr .r2)), 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [keyR, outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
    · simpa only [g₁] using keyFit
    · simpa only [g₁] using outputFit
  apply body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ keyKept) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨(State.addr (s.gpr .r2)), 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [outputR, g₁] at h
    exact h
  have saved₂ : Saved s s₂ := by
    intro i hi
    have sub : Region.Sub ⟨(State.addr (s.gpr .r3)) + BitVec.ofNat 64 (4 * i), 4⟩ ⟨(State.addr (s.gpr .r3)), 512⟩ :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₂.readW (a := (State.addr (s.gpr .r3)) + BitVec.ofNat 64 (4 * i)) (w := 32)
      (r := ⟨(State.addr (s.gpr .r3)) + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (outputScratch.sub_right sub).symm)
      (by decide)
    rw [g₂ .r3 (by decide)]
    have saved₁ := h₁.2.2.2.1 i hi
    rw [g₁] at saved₁
    exact mem.trans saved₁
  have scratchReads : ∀ i < 9, InRegions (s₂.rd ++ s₂.wr) ((State.addr (s₂.gpr .r3)) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .r3 (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (restore_ok s s₂ saved₂ (by rw [g₂ .r3 (by decide)]; omega_using [scratchFit]) scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨(State.addr (s.gpr .r3)), 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨(State.addr (s.gpr .r3)), 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame ((State.addr (s.gpr .r0))) (s.gpr .r1).toNat
    scratchFrame (by have bound := (s.gpr .r1).isLt; omega_using [bound]) (by simpa using keyScratch)
  constructor
  · intro r hr
    have kept : ∀ r ∈ preserved, r ∈ Impl.TripleDes.Arm.Key.savedRegs ∨ r ∈ keyKept := by decide
    rcases kept r hr with saved | other
    · exact h₃.1 r saved
    · exact (h₃.2.reg r (by revert other; cases r <;> decide)).trans (g₂ r other)
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem ((State.addr (s.gpr .r0))) (s.gpr .r1).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem ((State.addr (s.gpr .r2))) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.Arm.Key

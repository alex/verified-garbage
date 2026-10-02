import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Contract

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.AArch64.Key.expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, valid⟩ := hs
  have scratchWrites : ∀ i < 4, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x3, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.AArch64.Key.expandKey]
  apply WP.seq
  apply WP.mono (save_ok s scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .x1)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨s.gpr .x2, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [keyR, outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
  apply body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ keyKept) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨s.gpr .x2, 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [outputR, g₁] at h
    exact h
  have saved₂ : Saved s s₂ := by
    intro i hi
    have sub : Region.Sub ⟨s.gpr .x3 + BitVec.ofNat 64 (8 * i), 8⟩ ⟨s.gpr .x3, 512⟩ :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₂.readW (a := s.gpr .x3 + BitVec.ofNat 64 (8 * i)) (w := 64)
      (r := ⟨s.gpr .x3 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (outputScratch.sub_right sub).symm)
      (by decide)
    rw [g₂ .x3 (by decide)]
    have saved₁ := h₁.2.2.2.1 i hi
    rw [g₁] at saved₁
    exact mem.trans saved₁
  have scratchReads : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .x3 (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (restore_ok s s₂ saved₂ scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨s.gpr .x3, 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨s.gpr .x3, 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (s.gpr .x0) (s.gpr .x1).toNat
    scratchFrame (Nat.le_of_lt (BitVec.isLt _)) (by simpa using keyScratch)
  constructor
  · intro r hr
    have kept : ∀ r ∈ preserved, r ∈ Impl.TripleDes.AArch64.Key.savedRegs ∨ r ∈ keyKept := by decide
    rcases kept r hr with saved | other
    · exact h₃.1 r saved
    · exact (h₃.2.reg r (by revert other; cases r <;> decide)).trans (g₂ r other)
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (s.gpr .x0) (s.gpr .x1).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem (s.gpr .x2) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.AArch64.Key

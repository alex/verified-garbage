import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Contract

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.AArch64.Ecb.ecb d) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 1024) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .x3, 1024⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.TripleDes.AArch64.Ecb.ecb]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s (writes 512 (by decide)) (writes 520 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, count₂, buf₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at count₂ buf₂
  have key₂ := (keep₂.reg .x0 (by decide)).trans (g₁ .x0)
  have data₂ := (keep₂.reg .x1 (by decide)).trans (g₁ .x1)
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨s.gpr .x3, 1024⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (s.gpr .x0) scratchFrame
    (by simpa using keyBuf)
  have initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (s.gpr .x1) (s.gpr .x2).toNat
    (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .x2).toNat := by
    constructor
    · simp only [keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [dataR, bufR, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .x2).toNat (by omega) hp₂
    (by simpa using count₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .x2 (by decide) (by decide) (by decide)).trans buf₂
  have readable (i : Nat) (hi : i + 8 ≤ 1024) :
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x2 + BitVec.ofNat 64 i) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have counter : s₃.mem.readW (s₃.gpr .x2 + BitVec.ofNat 64 512) 64 = s.gpr .x23 := by
    have h := h₃.scratchRead hp₂ 512 (by decide)
    rw [buf₂, mem₂, savedMem_counter] at h
    rw [buf₃]; exact h
  have link : s₃.mem.readW (s₃.gpr .x2 + BitVec.ofNat 64 520) 64 = s.gpr .x30 := by
    have h := h₃.scratchRead hp₂ 520 (by decide)
    rw [buf₂, mem₂, savedMem_link] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, counter₄, link₄, keep₄⟩ := restore_ok s₃ (s.gpr .x23) (s.gpr .x30)
    (readable 512 (by decide)) (readable 520 (by decide)) counter link
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hc : r = .x23
    · subst r; exact counter₄
    by_cases hl : r = .x30
    · subst r; exact link₄
    have hsaved : ∀ r ∈ preserved, r ≠ .x30 → r ∈ savedAcrossCall := by decide
    rw [keep₄.reg r (by simp [hc, hl]), h₃.callee r (hsaved r hr hl) hc]
    have sep : ∀ r ∈ preserved, r ≠ .x23 → r ∉ [.x23, .x2] := by decide
    exact (keep₂.reg r (sep r hr hc)).trans (g₁ r)
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (s.gpr .x1) (s.gpr .x2).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.AArch64.Ecb

import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Contract

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.Arm.Ecb.ecb d) s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit, keyFit, bufFit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 1024) :
      InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (s.gpr .r3), 1024⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.TripleDes.Arm.Ecb.ecb]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s bufFit (writes 512 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at count₂ buf₂ flag₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans (g₁ .r0)
  have data₂ := (keep₂.reg .r1 (by decide)).trans (g₁ .r1)
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨State.addr (s.gpr .r3), 1024⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (State.addr (s.gpr .r0)) scratchFrame
    (by simpa using keyBuf)
  have initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (State.addr (s.gpr .r1)) (s.gpr .r2).toNat
    (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .r2).toNat := by
    constructor
    · simp only [keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [dataR, bufR, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [key₂]; exact keyFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
  have flag : zeroCount s₂ = some (decide ((s.gpr .r2).toNat = 0)) := by
    have hz := counter_zero (s.gpr .r2).toNat (s.gpr .r2).isLt
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hz
    exact flag₂.trans (congrArg some hz)
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .r2).toNat (by omega_using [fit]) hp₂
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using count₂) flag)
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .r2 (by decide) (by decide) (by decide)).trans buf₂
  have readable : InRegions (s₃.rd ++ s₃.wr)
      (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 512) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes 512 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have link : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 512) 32 = s.gpr .lr := by
    have h := h₃.scratchRead hp₂ 512 (by decide)
    rw [buf₂, mem₂, savedMem_link] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, link₄, keep₄⟩ := restore_ok s₃ (s.gpr .lr)
    (by rw [buf₃]; exact bufFit) readable link
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hl : r = .lr
    · subst r; exact link₄
    have saved : ∀ r ∈ preserved, r ≠ .lr → r ∈ savedAcrossCall ∧ r ≠ .r3 := by decide
    rw [keep₄.reg r (by simpa only [List.mem_singleton] using hl),
      h₃.callee r (saved r hr hl).1 (saved r hr hl).2]
    have sep : ∀ r ∈ preserved, r ≠ .lr → r ∉ [.r12, .r3, .r2] := by decide
    exact (keep₂.reg r (sep r hr hl)).trans (g₁ r)
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.Arm.Ecb

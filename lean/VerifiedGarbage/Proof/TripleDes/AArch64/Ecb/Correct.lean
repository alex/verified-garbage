import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Spill

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
  rw [save_eq]
  refine Spill.save_ok (by decide) (fun p hp => writes p.2 (by revert p; decide)) ?_
  obtain ⟨s₂, run₂, count₂, buf₂, keep₂⟩ := setup_ok { s with mem := savedMem s }
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₂ : s₂.gpr .x0 = s.gpr .x0 := keep₂.reg .x0 (by decide)
  have data₂ : s₂.gpr .x1 = s.gpr .x1 := keep₂.reg .x1 (by decide)
  have rd₂ : s₂.rd = s.rd := keep₂.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem
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
  have hsv : Spill.Saved (s₃.gpr .x2) s.gpr saved s₃.mem := fun p hp => by
    have h := h₃.scratchRead hp₂ p.2 (by revert p; decide)
    rw [buf₂, mem₂] at h
    rw [buf₃, h]
    exact Spill.saveMem_saved (by decide) _ _ _ p hp
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (fun p hp => readable p.2 (by revert p; decide)) hsv) fun s₄ h₄ => ?_
  constructor
  · intro r hr
    by_cases hs : r ∈ saved.map Prod.fst
    · exact h₄.gpr_of (.inl hs)
    have hb : r ≠ .x23 ∧ r ≠ .x30 := by
      simpa only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] using hs
    have hsaved : ∀ r ∈ preserved, r ≠ .x30 → r ∈ savedAcrossCall := by decide
    have sep : ∀ r ∈ preserved, r ≠ .x23 → r ∉ [.x23, .x2] := by decide
    rw [h₄.other r hs, h₃.callee r (hsaved r hr hb.2) hb.1]
    exact keep₂.reg r (sep r hr hb.1)
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (s.gpr .x1) (s.gpr .x2).toNat = _
    rw [h₄.mem]; exact out

end VG.Proof.TripleDes.AArch64.Ecb

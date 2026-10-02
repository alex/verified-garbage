import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Contract

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.X86_64.Ecb.ecb d) s (fun s' => gprPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf,
    retData, retBuf, stackKey, stackData, stackBuf, fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 1024) : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .rcx, 1024⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.TripleDes.X86_64.Ecb.ecb]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s (writes 512 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at count₂ buf₂ flag₂
  have key₂ := (keep₂.reg .rdi (by decide)).trans (g₁ .rdi)
  have data₂ := (keep₂.reg .rsi (by decide)).trans (g₁ .rsi)
  have sp₂ := (keep₂.reg .rsp (by decide)).trans (g₁ .rsp)
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨s.gpr .rcx, 1024⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (s.gpr .rdi) scratchFrame
    (by simpa using keyBuf)
  have initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (s.gpr .rsi) (s.gpr .rdx).toNat
    (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .rdx).toNat := by
    constructor
    · simp only [keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [dataR, bufR, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .rdx).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .rdx (by decide) (by decide) (by decide)).trans buf₂
  have readable : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdx + BitVec.ofNat 64 512) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes 512 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have value : s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 512) 64 = s.gpr .rbp := by
    have h := h₃.scratchRead hp₂
    rw [buf₂, mem₂, savedMem_rbp] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, rbp₄, keep₄⟩ := restore_ok s₃ (s.gpr .rbp) readable value
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      by_cases hp : r = .rbp
      · subst r; exact rbp₄
      · rw [keep₄.reg r (by simpa using hp), h₃.callee r hr hp]
        have sep : ∀ r ∈ calleeSaved, r ≠ .rbp → r ∉ [.rbp, .rdx] := by decide
        exact (keep₂.reg r (sep r hr hp)).trans (g₁ r)
    · let rs : List Region := [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩,
        ⟨s.gpr .rcx, 1024⟩, below (s.gpr .rsp) 8]
      have loopFrame : Frame rs s₂.mem s₃.mem := by
        have h := h₃.mem
        simp only [loopWrites, dataR, stackR, data₂, buf₂, sp₂] at h
        apply h.sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, by simp [rs], fun _ h => h⟩
        · exact ⟨⟨s.gpr .rcx, 1024⟩, by simp [rs], Region.sub_prefix (by decide)⟩
        · exact ⟨below (s.gpr .rsp) 8, by simp [rs], fun _ h => h⟩
      have frame : Frame rs s.mem s₄.mem := by
        rw [keep₄.mem]
        exact (scratchFrame.mono (by simp [rs])).trans loopFrame
      apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (hn := by decide)
      have stackSep : (Region.mk (s.gpr .rsp) 8).Disjoint (below (s.gpr .rsp) 8) :=
        Offset.base_disjoint_below _ (by decide : 8 + 8 ≤ 2 ^ 64)
      simpa only [rs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
        And.intro retData (And.intro retBuf stackSep)
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (s.gpr .rsi) (s.gpr .rdx).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.X86_64.Ecb

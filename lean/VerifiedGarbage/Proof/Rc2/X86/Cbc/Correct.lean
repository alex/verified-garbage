import VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.X86.Cbc.cbc d) s (fun s' => abiPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.Rc2.X86.Cbc.cbc]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    have ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega)⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have initialKey := scheduleAt_frame scratchFrame (addr32 (arg s 0)) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (addr32 (arg s 1)) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (addr32 (arg s 2)) (arg s 3).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (arg s 3).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .ebp (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 i) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v0 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 264) 32 = s.gpr .ebp := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_ebp, g₀ .ebp (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v1 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 268) 32 = s.gpr .ebx := by
    have h := h₃.scratchRead hp₂ 268 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_ebx, g₀ .ebx (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v2 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 272) 32 = s.gpr .esi := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_esi, g₀ .esi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v3 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 276) 32 = s.gpr .edi := by
    have h := h₃.scratchRead hp₂ 276 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_edi, g₀ .edi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s₃ s.gpr (by rw [buf₃]; exact bufFit)
    (reads 264 (by decide)) v0    (reads 268 (by decide)) v1    (reads 272 (by decide)) v2    (reads 276 (by decide)) v3
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      by_cases saved : r ∈ callerSaved
      · exact saved₄ r saved
      · have eqSp : r = .esp := by cases r <;> simp_all [calleeSaved, callerSaved]
        subst r
        rw [keep₄.reg .esp (by decide), h₃.reg .esp (by decide) (by decide) (by decide), sp₂]
    · have stackRet : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 16) := by
        change (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint ⟨_, 16⟩
        rw [Taint.sub_setWidth stackLo]
        exact Offset.base_disjoint_below _ (by decide)
      have frameLoop := h₃.mem
      have retSep : ∀ r ∈ loopWrites s₂ (arg s 3).toNat, (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint r := by
        simpa only [loopWrites, ivR, dataR, stackR, iv₂, data₂, buf₂, sp₂,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro retIv (And.intro retData (And.intro (retBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) stackRet))
      change s₄.mem.readW (addr32 (s.gpr .esp)) 32 = s.mem.readW (addr32 (s.gpr .esp)) 32
      rw [keep₄.mem, frameLoop.readW (Region.contains_self _ _) retSep (by decide),
        scratchFrame.readW (Region.contains_self _ _) (by simpa using retBuf) (by decide)]
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

end VG.Proof.Rc2.X86.Cbc

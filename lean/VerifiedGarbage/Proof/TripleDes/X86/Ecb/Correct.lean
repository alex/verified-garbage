import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Contract

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)

theorem counter_zero (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact BitVec.eq_of_toNat_eq (show x.toNat = (0 : BitVec 32).toNat from h)

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.X86.Ecb.ecb d) s (fun s' => abiPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨rd, wr, keyData, keyBuf, dataBuf, argsData, argsBuf, retData, retBuf,
    stackKey, stackData, stackBuf, keyFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 1024) : InRegions s.wr
      (addr32 (arg s 3) + BitVec.ofNat 64 i) 4 := by
    rw [wr]
    exact ⟨⟨addr32 (arg s 3), 1024⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  have argRead (i : Nat) (hlo : 1 ≤ i) (hhi : i ≤ 4) :
      InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    rw [rd, wr, wordAddr, addr_eq (by omega_using [spFit, hhi])]
    have hc := argContainsCount s 4 spFit (i - 1) (by omega_using [hlo, hhi])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hlo]] at hc
    exact ⟨⟨argAddr s 0, 16⟩, by simp, hc⟩
  rw [Impl.TripleDes.X86.Ecb.ecb]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (argRead 4 (by decide) (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa only [List.mem_singleton] using hr)
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit) (by
    intro k hk
    rw [keep₀.wr, buf₀, addr_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> omega_using [bufFit])]
    exact writes k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 3), 1024⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have args₁ := VG.Proof.Rc2.X86.arguments_frame 4 saveFrame sp₁ spFit
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact argsBuf)
  have reads₁ : ∀ i ∈ [1, 2, 3], InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .esp) i) 4 := by
    intro i hi
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, sp₁]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact argRead 1 (by decide) (by decide)
    · exact argRead 2 (by decide) (by decide)
    · exact argRead 3 (by decide) (by decide)
  obtain ⟨s₂, run₂, buf₂, key₂, data₂, count₂, flag₂, keep₂⟩ := setup_ok s₁ reads₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at data₂
  rw [args₁ 2 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨addr32 (arg s 3), 1024⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (addr32 (arg s 0)) scratchFrame
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact keyBuf)
  have initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (addr32 (arg s 1)) (arg s 2).toNat
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact dataBuf)
  have hp₂ : StepPre s₂ (arg s 2).toNat := by
    constructor
    · simp only [Covers, keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, rd, wr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [dataR, bufR, data₂, buf₂, wr₂, wr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [key₂]; exact keyFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · rw [sp₂]; exact stackLo
    · simpa only [keyR, sp₂, key₂] using stackKey
    · simpa only [dataR, sp₂, data₂] using stackData
    · simpa only [bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (arg s 2).toNat (by omega_using [fit]) hp₂
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using count₂)
    (flag₂.trans (congrArg some (counter_zero (arg s 2)))))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .ebp (by decide) (by decide) (by decide)).trans buf₂
  have reads₃ : ∀ k ∈ [512, 516, 520, 524], InRegions (s₃.rd ++ s₃.wr) (addr (s₃.gpr .ebp) k) 4 := by
    intro k hk
    have bound : k + 4 ≤ 1024 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    rw [rd₃, wr₃, buf₃, addr_eq (by omega_using [bufFit, bound])]
    obtain ⟨r, hr, hc⟩ := writes k bound
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have stored₃ : ∀ i < 4, s₃.mem.readW (addr (s₃.gpr .ebp) (512 + 4 * i)) 32 = s.gpr (savedReg i) := by
    intro i hi
    have h := h₃.scratchRead hp₂ (512 + 4 * i) (by omega_using [hi])
    rw [buf₂, mem₂, ← buf₀, savedMem_read s₀ i hi] at h
    rw [buf₀] at h
    rw [buf₃, addr_eq (by omega_using [bufFit, hi])]
    have reg : savedReg i ≠ .eax := (show ∀ i < 4, savedReg i ≠ .eax by decide) i hi
    exact h.trans (g₀ _ reg)
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s s₃ reads₃ stored₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      have regs : ∀ r ∈ calleeSaved, r ∈ savedRegs ∨ r = .esp := by decide
      rcases regs r hr with saved | rfl
      · exact saved₄ r saved
      · rw [keep₄.reg .esp (by decide), h₃.reg .esp (by decide) (by decide) (by decide), sp₂]
    · have stackRet : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 16) := by
        change (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint ⟨_, 16⟩
        rw [VG.X86.Taint.sub_setWidth stackLo]
        exact Offset.base_disjoint_below _ (by decide)
      have retSep : ∀ r ∈ loopWrites s₂ (arg s 2).toNat, (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint r := by
        simpa only [loopWrites, dataR, data₂, buf₂, sp₂,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro retData (And.intro (retBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024))) stackRet)
      change s₄.mem.readW (addr32 (s.gpr .esp)) 32 = s.mem.readW (addr32 (s.gpr .esp)) 32
      rw [keep₄.mem, h₃.mem.readW (Region.contains_self _ _) retSep (by decide),
        scratchFrame.readW (Region.contains_self _ _) (by
          intro r hr; obtain rfl := List.mem_singleton.mp hr; exact retBuf) (by decide)]
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (addr32 (arg s 1)) (arg s 2).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.X86.Ecb

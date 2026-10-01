import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), (arg s 1).toNat⟩
    let out : Region := ⟨addr32 (arg s 3), 128⟩
    let scratch : Region := ⟨addr32 (arg s 4), 512⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    s.rd = [key, args] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint out ∧
      (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint scratch ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 128 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      Spec.Rc2.validKey (arg s 1).toNat (arg s 2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (addr32 (arg s 3)) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat) (arg s 2).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => abiPreserved s s' ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, argsOut, argsScratch, retOut, retScratch, keyFit, outFit, scratchFit, spFit, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have argRead (st : State) (rd : st.rd = s.rd) (wr : st.wr = s.wr)
      (sp : st.gpr .esp = s.gpr .esp) : ∀ i < 5, InRegions (st.rd ++ st.wr) (argAddr st i) 4 := by
    intro i hi
    have fit : (st.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by rw [sp]; exact spFit
    rw [argAddr_eq st i (by omega), sp, rd, wr, hrd, hwr]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i hi⟩
  rw [expandKey]
  apply WP.seq
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadArg_ok s .eax 4 (argRead s rfl rfl rfl 4 (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have gpr₀ (r : Reg) (hr : r ≠ .eax) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (saveCode_ok s₀ .eax savedReg 4 (by decide)
    (by rw [scratch₀]; omega) (by rw [keep₀.wr, scratch₀]; exact writes))
  intro s₁ h₁
  have sp₁ : s₁.gpr .esp = s.gpr .esp := by rw [h₁.1]; exact gpr₀ .esp (by decide)
  have savedFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2, keep₀.mem, scratch₀]
    apply (saveMem_frame_le _ _ _ 4 64 (by decide) (by decide)).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨addr32 (arg s 4), 512⟩, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have args₁ : ∀ i < 5, arg s₁ i = arg s i :=
    args_frame savedFrame sp₁ spFit (by simpa using argsScratch)
  apply WP.mono (pinKey_ok s₁ (argRead s₁ (h₁.2.1.trans keep₀.rd) (h₁.2.2.1.trans keep₀.wr) sp₁))
  intro s₂ ⟨key₂, len₂, ptr₂, zero₂, keep₂⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at len₂
  rw [args₁ 3 (by decide)] at ptr₂
  have scratchFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem]; exact savedFrame
  have sp₂ : s₂.gpr .esp = s.gpr .esp := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (addr32 (s₂.gpr .ebp)) (arg s 1).toNat =
      Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega)
  have read₂ : ∀ i < (arg s 1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨addr32 (arg s 0), (arg s 1).toNat⟩, by simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (addr32 (s₂.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨addr32 (arg s 3), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (arg s 1).toNat ht ht' (by rw [key₂]; exact keyFit) (by rw [ptr₂]; exact outFit)
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (addr32 (s₃.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .edi (by decide)]; exact write₂
  have sp₃ : s₃.gpr .esp = s.gpr .esp := (h₃.1.reg .esp (by decide)).trans sp₂
  have argFrame₃ : Frame [⟨addr32 (arg s 4), 512⟩, ⟨addr32 (arg s 3), 128⟩] s.mem s₃.mem := by
    have outFrame₃ := h₃.1.mem
    rw [ptr₂] at outFrame₃
    exact (scratchFrame.mono (by simp)).trans (outFrame₃.mono (by simp))
  have args₃ := args_frame argFrame₃ sp₃ spFit (by simpa using And.intro argsScratch argsOut)
  apply WP.mono (expandReduce_ok s₃ _ (arg s 2).toNat hb hb'
    (by rw [h₃.1.reg .edi (by decide), ptr₂]; exact outFit)
    (argRead s₃ (h₃.1.rd.trans rd₂) (h₃.1.wr.trans wr₂) sp₃ 2 (by decide))
    (by simpa only [arg, argAddr, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_toNat, BitVec.setWidth_eq, addr32, BitVec.ofNat_eq_ofNat] using args₃ 2 (by decide))
    write₃ (by rw [h₃.1.reg .edi (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨addr32 (arg s 3), 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have sp₄ : s₄.gpr .esp = s.gpr .esp := (core.reg .esp (by decide)).trans sp₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (addr32 (arg s 3))
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat) (arg s 2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .edi (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat).length = (arg s 1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  rw [WP.block_append_iff]
  have frame₄ : Frame [⟨addr32 (arg s 4), 512⟩, ⟨addr32 (arg s 3), 128⟩] s.mem s₄.mem :=
    (scratchFrame.mono (by simp)).trans (outFrame.mono (by simp))
  have args₄ := args_frame frame₄ sp₄ spFit (by simpa using And.intro argsScratch argsOut)
  obtain ⟨s₅, run₅, base₅, keep₅⟩ := loadArg_ok s₄ .eax 4 (argRead s₄ rd₄ wr₄ sp₄ 4 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [args₄ 4 (by decide)] at base₅
  have rd₅ := keep₅.rd.trans rd₄
  have wr₅ := keep₅.wr.trans wr₄
  have scratchRead : ∀ i ∈ List.range 4,
      InRegions (s₅.rd ++ s₅.wr) (addr32 (s₅.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [rd₅, wr₅, base₅, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored : ∀ i ∈ List.range 4,
      s₅.mem.readW (addr32 (s₅.gpr .eax) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [keep₅.mem, base₅, outFrame.readW (r := ⟨addr32 (arg s 4), 512⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀]
    rw [saveMem_read _ _ _ 4 (by decide) i bound]
    exact gpr₀ _ (by
      have sep : ∀ i ∈ List.range 4, savedReg i ≠ .eax := by decide
      exact sep i hi)
  rw [keyRestore_eq]
  apply WP.mono (restoreCode_ok s₅ .eax savedReg (List.range 4) s.gpr (by rw [base₅]; omega)
    (by decide) (by decide) scratchRead stored)
  intro s₆ h₆
  constructor
  · constructor
    · intro r hr
      by_cases he : r = .esp
      · subst r
        exact (h₆.2.reg .esp (by decide)).trans ((keep₅.reg .esp (by decide)).trans sp₄)
      · exact h₆.1 r (by
          have covered : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ (List.range 4).map savedReg := by decide
          exact covered r hr he)
    · rw [h₆.2.mem, keep₅.mem]
      exact frame₄.readW (Region.contains_self _ _) (by simpa [addr32] using And.intro retScratch retOut) (by decide)
  · change Spec.Rc2.scheduleAt s₆.mem (addr32 (arg s 3)) = _
    rw [h₆.2.mem, keep₅.mem]
    exact scheduleAt_expanded expanded


end VG.Proof.Rc2.X86

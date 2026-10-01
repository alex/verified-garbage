import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # RC2 block correctness and the x86 calling convention -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def blockSavedReg (i : Nat) : Reg := blockSaved.getD i .eax

theorem blockSave_eq : blockSave = saveCode .eax blockSavedReg 5 := rfl

theorem blockRestore_eq : blockRestore = restoreCode .eax blockSavedReg (List.range 5) := rfl

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 128⟩
    let data : Region := ⟨addr32 (arg s 1), 8⟩
    let scratch : Region := ⟨addr32 (arg s 2), 256⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := s'.gpr .ecx = s.gpr .ecx ∧ Spec.Rc2.blockAt s'.mem (addr32 (arg s 1)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) (Spec.Rc2.blockAt s.mem (addr32 (arg s 1)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => abiPreserved s s' ∧ (blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, retData, retScratch, keyFit, dataFit, scratchFit, spFit⟩ := hs
  have argRead (st : State) (rd : st.rd = s.rd) (wr : st.wr = s.wr)
      (sp : st.gpr .esp = s.gpr .esp) : ∀ i < 3, InRegions (st.rd ++ st.wr) (argAddr st i) 4 := by
    intro i hi
    have fit : (st.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by rw [sp]; exact spFit
    rw [argAddr_eq st i (by omega), sp, rd, wr, hrd, hwr]
    exact ⟨⟨argAddr s 0, 12⟩, by simp, argContainsCount s 3 spFit i hi⟩
  have writes : ∀ i < 5, InRegions s.wr (addr32 (arg s 2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨addr32 (arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadArg_ok s .eax 2 (argRead s rfl rfl rfl 2 (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  rw [WP.block_append_iff, blockSave_eq]
  apply WP.mono (saveCode_ok s₀ .eax blockSavedReg 5 (by decide)
    (by rw [scratch₀]; exact scratchFit) (by rw [keep₀.wr, scratch₀]; exact writes))
  intro s₁ h₁
  have gpr₀ (r : Reg) (hr : r ≠ .eax) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := by rw [h₁.1]; exact gpr₀ .esp (by decide)
  have savedFrame : Frame [⟨addr32 (arg s 2), 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2, keep₀.mem, scratch₀]
    exact saveMem_frame_le s.mem (addr32 (arg s 2)) (fun i => s₀.gpr (blockSavedReg i)) 5 64 (by decide) (by decide)
  have args₁ := arguments_frame 3 savedFrame sp₁ spFit (by simpa using argsScratch)
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, scratch₂, data₂, keep₂⟩ := pinBlock_ok s₁
    (argRead s₁ (h₁.2.1.trans keep₀.rd) (h₁.2.2.1.trans keep₀.wr) sp₁ 1 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [h₁.1, scratch₀] at scratch₂
  rw [args₁ 1 (by decide)] at data₂
  have sp₂ : s₂.gpr .esp = s.gpr .esp := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  have frame₂ : Frame [⟨addr32 (arg s 2), 256⟩] s.mem s₂.mem := by rw [keep₂.mem]; exact savedFrame
  have args₂ := arguments_frame 3 frame₂ sp₂ spFit (by simpa using argsScratch)
  have base₂ : wordBase s₂ = addr32 (arg s 2) + 64 := by unfold wordBase; rw [scratch₂]
  have wordsSub : Region.Sub ⟨wordBase s₂, 16⟩ ⟨addr32 (arg s 2), 256⟩ := by
    rw [base₂]; exact Offset.sub_base (addr32 (arg s 2)) (d := 64) (n := 16) (k := 256) (by decide)
  have dataWords : (Region.mk (addr32 (arg s 1)) 8).Disjoint ⟨wordBase s₂, 16⟩ := by
    intro a ha hb; exact dataSep a ha (wordsSub a hb)
  have env₂ : RoundEnv s₂ := by
    constructor
    · rw [scratch₂]; exact scratchFit
    · rw [args₂ 0 (by decide)]; exact keyFit
    · exact argRead s₂ rd₂ wr₂ sp₂ 0 (by decide)
    · intro i hi
      rw [args₂ 0 (by decide), rd₂, wr₂, hrd, hwr]
      exact ⟨⟨addr32 (arg s 0), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · intro i hi
      rw [wr₂, hwr, base₂, BitVec.add_assoc, show (64 : Addr) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]
      exact ⟨⟨addr32 (arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [args₂ 0 (by decide)]
      intro a ha hb; exact keySep a ha (wordsSub a hb)
    · have ae : argAddr s₂ 0 = argAddr s 0 := by unfold argAddr; rw [sp₂]
      rw [ae]
      intro a ha hb
      exact argsScratch a (Region.sub_prefix (by decide : 4 ≤ 12) a ha) (wordsSub a hb)
  have input₂ : Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .edi)) = Spec.Rc2.blockAt s.mem (addr32 (arg s 1)) := by
    rw [data₂]; exact blockAt_frame frame₂ _ (by simpa using dataSep)
  have schedule₂ : Spec.Rc2.scheduleAt s₂.mem (addr32 (arg s₂ 0)) = Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0)) := by
    rw [args₂ 0 (by decide)]; exact scheduleAt_frame frame₂ _ (by simpa using keySep)
  have dataRead₂ : ∀ i < 8, InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, data₂, hrd, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockLoad_ok s₂ (by rw [data₂]; exact dataFit) env₂.scratchFit dataRead₂ env₂.wordWrite
    (by rw [data₂]; exact dataWords))
  intro s₃ h₃
  rw [WP.block_append_iff]
  apply WP.mono (rounds_ok d s₃ _ h₃.1 (h₃.2.env env₂))
  intro s₄ h₄
  have core := h₃.2.trans h₄.2
  have env₄ := core.env env₂
  have sp₄ : s₄.gpr .esp = s.gpr .esp := (core.reg .esp (by decide)).trans sp₂
  have scratch₄ : s₄.gpr .ebp = arg s 2 := (core.reg .ebp (by decide)).trans scratch₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have frame₄ : Frame [⟨addr32 (arg s 2), 256⟩] s.mem s₄.mem :=
    frame₂.trans (core.mem.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_cons_self, wordsSub⟩))
  have args₄ := arguments_frame 3 frame₄ sp₄ spFit (by simpa using argsScratch)
  let v := (List.range 16).foldl (fun v j => roundSpec d
    (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (arg s 1))))
  have words₄ : MemWords s₄.mem (wordBase s₄) v := by
    have h := h₄.1
    rw [h₃.2.schedule env₂, schedule₂, input₂] at h
    exact h
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, data₅, keep₅⟩ := loadArg_ok s₄ .edi 1 (argRead s₄ rd₄ wr₄ sp₄ 1 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [args₄ 1 (by decide)] at data₅
  have base₅ : wordBase s₅ = wordBase s₄ := by unfold wordBase; rw [keep₅.reg .ebp (by decide)]
  have writable₅ : ∀ i < 8, InRegions s₅.wr (addr32 (s₅.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [keep₅.wr, wr₄, data₅, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockStore_ok s₅ v (by rw [keep₅.mem, base₅]; exact words₄)
    (by rw [data₅]; exact dataFit) (by rw [keep₅.reg .ebp (by decide)]; exact env₄.scratchFit)
    (by rw [keep₅.rd, keep₅.wr, base₅]; exact env₄.wordRead)
    (by rw [base₅, core.base, data₅]; exact dataWords.symm) writable₅)
  intro s₆ h₆
  have mem₆ : s₆.mem = s₄.mem.writeW (addr32 (arg s 1)) (pack v) := by rw [h₆.mem, keep₅.mem, data₅]
  have scratch₆ : s₆.gpr .ebp = arg s 2 := (h₆.reg .ebp (by decide)).trans ((keep₅.reg .ebp (by decide)).trans scratch₄)
  have sp₆ : s₆.gpr .esp = s.gpr .esp := (h₆.reg .esp (by decide)).trans ((keep₅.reg .esp (by decide)).trans sp₄)
  have rd₆ := h₆.rd.trans (keep₅.rd.trans rd₄)
  have wr₆ := h₆.wr.trans (keep₅.wr.trans wr₄)
  rw [WP.block_append_iff]
  obtain ⟨s₇, run₇, base₇, keep₇⟩ := blockScratchBase_ok s₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  rw [scratch₆] at base₇
  have reads₇ : ∀ i ∈ List.range 5, InRegions (s₇.rd ++ s₇.wr) (addr32 (s₇.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [keep₇.rd, keep₇.wr, rd₆, wr₆, base₇, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨addr32 (arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored₇ : ∀ i ∈ List.range 5, s₇.mem.readW (addr32 (s₇.gpr .eax) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (blockSavedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [keep₇.mem, mem₆, base₇, Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _)) (by decide)]
    have sep : (Region.mk (addr32 (arg s 2)) 20).Disjoint ⟨wordBase s₂, 16⟩ := by
      rw [base₂]; exact (Offset.disjoint_base (addr32 (arg s 2)) (d := 64) (n := 16) (k := 20) (by decide) (by decide)).symm
    rw [core.mem.readW (r := ⟨addr32 (arg s 2), 20⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using sep) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀, saveMem_read _ _ _ 5 (by decide) i bound]
    exact gpr₀ _ (by
      have fact : ∀ i ∈ List.range 5, blockSavedReg i ≠ .eax := by decide
      exact fact i hi)
  rw [blockRestore_eq]
  apply WP.mono (restoreCode_ok s₇ .eax blockSavedReg (List.range 5) s.gpr
    (by rw [base₇]; exact scratchFit) (by decide) (by decide) reads₇ stored₇)
  intro s₈ h₈
  constructor
  · constructor
    · intro r hr
      by_cases he : r = .esp
      · subst r
        exact (h₈.2.reg .esp (by decide)).trans ((keep₇.reg .esp (by decide)).trans sp₆)
      · exact h₈.1 r (by
          have fact : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ (List.range 5).map blockSavedReg := by decide
          exact fact r hr he)
    · rw [h₈.2.mem, keep₇.mem, mem₆, Mem.readW_writeW_sep
        (retData.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
      exact frame₄.readW (Region.contains_self _ _) (by simpa [addr32] using retScratch) (by decide)
  · refine ⟨h₈.1 .ecx (by decide), ?_⟩
    change Spec.Rc2.blockAt s₈.mem (addr32 (arg s 1)) = _
    rw [h₈.2.mem, keep₇.mem, mem₆, blockAt_write64, cipher_rounds]

end VG.Proof.Rc2.X86

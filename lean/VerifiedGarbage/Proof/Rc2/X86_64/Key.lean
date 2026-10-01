import VerifiedGarbage.Proof.Rc2.X86_64.KeyIO
import VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let out : Region := ⟨s.gpr .rcx, 128⟩
    let scratch : Region := ⟨s.gpr .r8, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      Spec.Rc2.validKey (s.gpr .rsi).toNat (s.gpr .rdx).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .rcx) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (s.gpr .rdx).toNat
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8]

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => gprPreserved s s' ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, retOut, retScratch, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 6, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [expandKey]
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (saveCode_ok s .r8 savedReg 6 writes)
  intro s₁ h₁
  obtain ⟨s₂, run₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have scratchFrame : Frame [⟨s.gpr .r8, 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.2.2.2]
    exact saveMem_frame_le _ _ _ 6 64 (by decide) (by decide)
  rw [h₁.1] at key₂ len₂ ptr₂ bits₂
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans h₁.2.1
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans h₁.2.2.1
  have r8₂ : s₂.gpr .r8 = s.gpr .r8 := (keep₂.reg .r8 (by decide)).trans (congrFun h₁.1 .r8)
  have rsp₂ : s₂.gpr .rsp = s.gpr .rsp := (keep₂.reg .rsp (by decide)).trans (congrFun h₁.1 .rsp)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (s₂.gpr .r12) (s.gpr .rsi).toNat =
      Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega)
  have read₂ : ∀ i < (s.gpr .rsi).toNat,
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r12 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (s₂.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨s.gpr .rcx, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have lookup₂ : InRegions s₂.wr (s₂.gpr .r8 + BitVec.ofNat 64 64) 16 := by
    rw [wr₂, r8₂, hwr]
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ lookup₂ (s.gpr .rsi).toNat ht ht'
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (s₃.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .r14 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ (by
    rw [h₃.1.wr, h₃.1.reg .r8 (by decide)]; exact lookup₂) _ (s.gpr .rdx).toNat hb hb'
    (by simpa using (h₃.1.reg .r15 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .r14 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨s.gpr .rcx, 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .r8 = s.gpr .r8 := (core.reg .r8 (by decide)).trans r8₂
  have rsp₄ : s₄.gpr .rsp = s.gpr .rsp := (core.reg .rsp (by decide)).trans rsp₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (s.gpr .rcx)
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (s.gpr .rdx).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .r14 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat).length = (s.gpr .rsi).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  have scratchRead : ∀ i ∈ List.range 6,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .r8 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, r8₄, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored : ∀ i ∈ List.range 6,
      s₄.mem.readW (s₄.gpr .r8 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [r8₄, outFrame.readW (r := ⟨s.gpr .r8, 512⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2]
    exact saveMem_read _ _ _ 6 (by decide) i bound
  rw [keyRestore_eq]
  apply WP.mono (restoreCode_ok s₄ .r8 savedReg (List.range 6) s.gpr
    (by decide) scratchRead stored)
  intro s₅ h₅
  constructor
  · constructor
    · intro r hr
      by_cases hm : r ∈ (List.range 6).map savedReg
      · exact h₅.1 r hm
      · have covered : ∀ r ∈ calleeSaved, r ∈ (List.range 6).map savedReg ∨ r = .rsp := by decide
        have he := (covered r hr).resolve_left hm
        subst r
        exact (h₅.2.reg .rsp hm).trans rsp₄
    · have frame : Frame [⟨s.gpr .rcx, 128⟩, ⟨s.gpr .r8, 512⟩] s.mem s₅.mem := by
        rw [h₅.2.mem]
        exact (scratchFrame.mono (fun _ hr => List.mem_cons_of_mem _ hr)).trans
          (outFrame.mono (by simp))
      exact frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h
          · subst r; exact retOut
          · subst r; exact retScratch) (by decide)
  · change Spec.Rc2.scheduleAt s₅.mem (s.gpr .rcx) = _
    rw [h₅.2.mem]
    exact scheduleAt_expanded expanded

def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 8 | .rcx => 0x2000 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_body_correct s hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 := by
  simp [PublicRegs]

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct key_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argRegs,
    keyContract, publicRegs_five, Spec.Rc2.validKey] [keySatState] using keySatState

end VG.Proof.Rc2.X86_64

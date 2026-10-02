import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Rc2.AArch64.KeyIO
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let out : Region := ⟨s.gpr .x3, 128⟩
    let scratch : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [key] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧
      Spec.Rc2.validKey (s.gpr .x1).toNat (s.gpr .x2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .x3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (s.gpr .x2).toNat
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 6, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [expandKey]
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (Spill.save_wp (by decide) (Spill.forall_slots writes))
  intro s₁ h₁
  obtain ⟨s₂, run₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have scratchFrame : Frame [⟨s.gpr .x4, 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.mem]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  rw [h₁.gpr] at key₂ len₂ ptr₂ bits₂
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans h₁.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans h₁.wr
  have r8₂ : s₂.gpr .x4 = s.gpr .x4 := (keep₂.reg .x4 (by decide)).trans (congrFun h₁.gpr .x4)
  have other₂ : ∀ r ∈ coreRegs, r ≠ .x21 → s₂.gpr r = s.gpr r := by
    intro r hr hn
    have sep : ∀ r ∈ coreRegs, r ≠ .x21 → r ∉ saved := by decide
    exact (keep₂.reg r (sep r hr hn)).trans (congrFun h₁.gpr r)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (s₂.gpr .x19) (s.gpr .x1).toNat =
      Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega)
  have read₂ : ∀ i < (s.gpr .x1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x19 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (s₂.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨s.gpr .x3, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (s.gpr .x1).toNat ht ht'
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (s₃.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .x21 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ _ (s.gpr .x2).toNat hb hb'
    (by simpa using (h₃.1.reg .x22 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .x21 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨s.gpr .x3, 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .x4 = s.gpr .x4 := (core.reg .x4 (by decide)).trans r8₂
  have other₄ : ∀ r ∈ coreRegs, r ≠ .x21 → s₄.gpr r = s.gpr r := by
    intro r hr hn
    exact (core.reg r hr).trans (other₂ r hr hn)
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (s.gpr .x3)
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (s.gpr .x2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .x21 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat).length = (s.gpr .x1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  have scratchRead : ∀ i ∈ List.range 6,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x4 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, r8₄, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored : ∀ i ∈ List.range 6,
      s₄.mem.readW (s₄.gpr .x4 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [r8₄, outFrame.readW (r := ⟨s.gpr .x4, 512⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 6) (by decide) s.mem (s.gpr .x4) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots bound)
  rw [keyRestore_eq]
  apply WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (Spill.forall_slots fun i hi => scratchRead i (List.mem_range.mpr hi))
    (Spill.forall_slots fun i hi => stored i (List.mem_range.mpr hi)))
  intro s₅ h₅
  constructor
  · intro r hr
    by_cases hm : r ∈ (List.range 6).map savedReg
    · exact h₅.gpr_of (.inl (by rwa [Spill.slots_fst]))
    · have covered : ∀ r ∈ preserved, r ∉ (List.range 6).map savedReg →
          r ∈ coreRegs ∧ r ≠ .x21 := by decide
      obtain ⟨hc, hn⟩ := covered r hr hm
      exact (h₅.other r (by rwa [Spill.slots_fst])).trans (other₄ r hc hn)
  · change Spec.Rc2.scheduleAt s₅.mem (s.gpr .x3) = _
    rw [h₅.mem]
    exact scheduleAt_expanded expanded

def keySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 8 | .x3 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_body_correct s hs
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he⟩, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3, .x4] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 := by
  simp [PublicRegs]

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct key_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argRegs,
    keyContract, publicRegs_five, Spec.Rc2.validKey] [keySatState] using keySatState

end VG.Proof.Rc2.AArch64

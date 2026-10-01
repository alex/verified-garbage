import VerifiedGarbage.Proof.Rc2.AArch64.Save
import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Verified RC2 block encryption and decryption -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, 8⟩
    let scratch : Region := ⟨s.gpr .x2, 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))
  pub := PublicRegs [.x0, .x1, .x2]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x2, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  apply WP.mono (saveCode_ok s .x2 wordReg 4 (by decide) writes)
  intro s₁ h₁
  have scratchFrame : Frame [⟨s.gpr .x2, 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2]
    exact saveMem_frame_le _ _ _ 4 32 (by decide) (by decide)
  have input₁ : Spec.Rc2.blockAt s₁.mem (s₁.gpr .x1) = Spec.Rc2.blockAt s.mem (s.gpr .x1) := by
    rw [h₁.1]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (s₁.gpr .x0) =
      Spec.Rc2.scheduleAt s.mem (s.gpr .x0) := by
    rw [h₁.1]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1) 8 := by
    rw [h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockLoad_ok s₁ dataRead₁)
  intro s₂ h₂
  have read₂ : ∀ i < 128, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .x0 (by decide), h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .x0, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (rounds_ok d s₂ _ h₂.1 read₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans h₃.2
  have ptr₃ : s₃.gpr .x1 = s.gpr .x1 := (keep₂₃.reg .x1 (by decide)).trans (congrFun h₁.1 .x1)
  have writable₃ : InRegions s₃.wr (s₃.gpr .x1) 8 := by
    rw [keep₂₃.wr, h₁.2.2.1, hwr, ptr₃]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  let v := (List.range 16).foldl (fun v j => roundSpec d
    (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1)))
  have words₃ : Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .x0 (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (blockStore_ok s₃ v words₃ writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (s.gpr .x1) (pack v) := by rw [h₄.1, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.2.2.1.trans (keep₂₃.rd.trans h₁.2.1)
  have wr₄ : s₄.wr = s.wr := h₄.2.2.2.trans (keep₂₃.wr.trans h₁.2.2.1)
  have regs₄ (r : Reg) (hr : r ∉ roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.2.1 r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he <;> subst r <;> exact hr (by decide)), keep₂₃.reg r hr, h₁.1]
  have scratchRead₄ : ∀ i ∈ List.range 4,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, regs₄ .x2 (by decide), hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .x2, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have saved₄ : ∀ i ∈ List.range 4,
      s₄.mem.readW (s₄.gpr .x2 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (wordReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [mem₄, regs₄ .x2 (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _))
      (by decide), h₁.2.2.2]
    exact saveMem_read _ _ _ 4 (by decide) i bound
  apply WP.mono (restoreCode_ok s₄ .x2 wordReg (List.range 4) s.gpr
    (fun i hi => by have := List.mem_range.mp hi; omega)
    (fun i _ => (wordReg_separate i).2.2.1) scratchRead₄ saved₄)
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (s.gpr .x1) (pack v) := h₅.2.mem.trans mem₄
  constructor
  · intro r hr
    by_cases hm : r ∈ (List.range 4).map wordReg
    · exact h₅.1 r hm
    · rw [h₅.2.reg _ hm]
      have covered : ∀ r ∈ preserved,
          r ∈ (List.range 4).map wordReg ∨ r ∉ roundWrites := by decide
      exact regs₄ r ((covered r hr).resolve_left hm)
  · change Spec.Rc2.blockAt s₅.mem (s.gpr .x1) = _
    rw [finalMem, blockAt_write64, cipher_rounds]

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1⟩, hp⟩

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 := by
  simp [PublicRegs]

theorem encrypt_verified :
    Verified target encryptBlock (Spec.Rc2.encryptBlockContract abi) := by
  refine Verified.of_correct encrypt_correct (encryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argRegs,
    blockContract, publicRegs_three, cipher] [satState] using satState

theorem decrypt_verified :
    Verified target decryptBlock (Spec.Rc2.decryptBlockContract abi) := by
  refine Verified.of_correct decrypt_correct (decryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argRegs,
    blockContract, publicRegs_three, cipher] [satState] using satState

end VG.Proof.Rc2.AArch64

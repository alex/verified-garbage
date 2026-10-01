import VerifiedGarbage.Proof.Rc2.X86_64.Save
import VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Verified RC2 block encryption and decryption -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 8⟩
    let scratch : Region := ⟨s.gpr .rdx, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .rsi) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))
  pub := PublicRegs [.rdi, .rsi, .rdx]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => gprPreserved s s' ∧ (blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, retData, retScratch⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  apply WP.mono (saveCode_ok s .rdx wordReg 4 writes)
  intro s₁ h₁
  have scratchFrame : Frame [⟨s.gpr .rdx, 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2]
    exact saveMem_frame_le _ _ _ 4 32 (by decide) (by decide)
  have input₁ : Spec.Rc2.blockAt s₁.mem (s₁.gpr .rsi) = Spec.Rc2.blockAt s.mem (s.gpr .rsi) := by
    rw [h₁.1]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (s₁.gpr .rdi) =
      Spec.Rc2.scheduleAt s.mem (s.gpr .rdi) := by
    rw [h₁.1]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 8 := by
    rw [h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockLoad_ok s₁ dataRead₁)
  intro s₂ h₂
  have read₂ : ∀ i < 128, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .rdi (by decide), h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨s.gpr .rdi, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have scans₂ : ScanMemory s₂ := by
    refine ⟨read₂, ?_, ?_⟩
    · intro i hi
      rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .rdi (by decide), h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
      exact ⟨⟨s.gpr .rdi, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [h₂.2.wr, h₂.2.reg .rdx (by decide), h₁.1, h₁.2.2.1, hwr]
      exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  rw [WP.block_append_iff]
  apply WP.mono (rounds_ok d s₂ _ h₂.1 scans₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans h₃.2
  have ptr₃ : s₃.gpr .rsi = s.gpr .rsi := (keep₂₃.reg .rsi (by decide)).trans (congrFun h₁.1 .rsi)
  have writable₃ : InRegions s₃.wr (s₃.gpr .rsi) 8 := by
    rw [keep₂₃.wr, h₁.2.2.1, hwr, ptr₃]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  let v := (List.range 16).foldl (fun v j => roundSpec d
    (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .rsi)))
  have words₃ : Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .rdi (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (blockStore_ok s₃ v words₃ writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (s.gpr .rsi) (pack v) := by rw [h₄.1, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.2.2.1.trans (keep₂₃.rd.trans h₁.2.1)
  have wr₄ : s₄.wr = s.wr := h₄.2.2.2.trans (keep₂₃.wr.trans h₁.2.2.1)
  have regs₄ (r : Reg) (hr : r ∉ roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.2.1 r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he <;> subst r <;> exact hr (by decide)), keep₂₃.reg r hr, h₁.1]
  have scratchRead₄ : ∀ i ∈ List.range 4,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, regs₄ .rdx (by decide), hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .rdx, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have saved₄ : ∀ i ∈ List.range 4,
      s₄.mem.readW (s₄.gpr .rdx + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (wordReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [mem₄, regs₄ .rdx (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _))
      (by decide), h₁.2.2.2]
    exact saveMem_read _ _ _ 4 (by decide) i bound
  apply WP.mono (restoreCode_ok s₄ .rdx wordReg (List.range 4) s.gpr
    (fun i _ => (wordReg_separate i).2.2.1) scratchRead₄ saved₄)
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (s.gpr .rsi) (pack v) := h₅.2.mem.trans mem₄
  constructor
  · constructor
    · intro r hr
      by_cases hm : r ∈ (List.range 4).map wordReg
      · exact h₅.1 r hm
      · rw [h₅.2.reg _ hm]
        have covered : ∀ r ∈ calleeSaved,
            r ∈ (List.range 4).map wordReg ∨ r ∉ roundWrites := by decide
        exact regs₄ r ((covered r hr).resolve_left hm)
    · have frame₄ : Frame [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩] s.mem s₅.mem := by
        rw [finalMem]
        exact (scratchFrame.mono (fun _ hr => List.mem_cons_of_mem _ hr)).writeW
          List.mem_cons_self _ (Region.contains_self _ _)
      exact frame₄.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h
          · subst r; exact retData
          · subst r; exact retScratch)
        (by decide)
  · change Spec.Rc2.blockAt s₅.mem (s.gpr .rsi) = _
    rw [finalMem, blockAt_write64, cipher_rounds]

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx := by
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

end VG.Proof.Rc2.X86_64

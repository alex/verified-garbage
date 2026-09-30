import VerifiedGarbage.Proof.Rc2.Arm.Save
import VerifiedGarbage.Proof.Rc2.Arm.ConstantTime
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Verified RC2 block encryption and decryption -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def blockSavedReg (i : Nat) : Reg := blockSaved.getD i .r4

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  post s s' := Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))
  pub := PublicRegs [.r0, .r1, .r2]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, keyFit, dataFit, scratchFit⟩ := hs
  have writes : ∀ i < 8, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨State.addr (s.gpr .r2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  apply WP.mono (saveCode_ok s .r2 blockSavedReg 8 (by decide) scratchFit writes)
  intro s₁ h₁
  have scratchFrame : Frame [⟨State.addr (s.gpr .r2), 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2]
    exact saveMem_frame_le _ _ _ 8 64 (by decide) (by decide)
  have input₁ : Spec.Rc2.blockAt s₁.mem (State.addr (s₁.gpr .r1)) = Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [h₁.1]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (State.addr (s₁.gpr .r0)) =
      Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
    rw [h₁.1]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : ∀ i < 8,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r1) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h₁.1, h₁.2.1, h₁.2.2.1, hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (blockLoad_ok s₁ (by rw [h₁.1]; exact dataFit) dataRead₁)
  intro s₂ h₂
  have keyPtr₂ : s₂.gpr .r0 = s.gpr .r0 := (h₂.2.reg .r0 (by decide)).trans (congrFun h₁.1 .r0)
  have read₂ : ∀ i < 128, InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r0 + BitVec.ofNat 32 i)) 1 := by
    intro i hi
    rw [h₂.2.rd, h₂.2.wr, keyPtr₂, h₁.2.1, h₁.2.2.1, hrd, hwr, addr_add (by omega)]
    exact ⟨⟨State.addr (s.gpr .r0), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (rounds_ok d s₂ _ h₂.1 (by rw [keyPtr₂]; exact keyFit) read₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans h₃.2
  have ptr₃ : s₃.gpr .r1 = s.gpr .r1 := (keep₂₃.reg .r1 (by decide)).trans (congrFun h₁.1 .r1)
  have writable₃ : ∀ i < 8, InRegions s₃.wr (State.addr (s₃.gpr .r1) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [keep₂₃.wr, h₁.2.2.1, hwr, ptr₃]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  let v := (List.range 16).foldl (fun v j => roundSpec d
    (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))))
  have words₃ : Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .r0 (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (blockStore_ok s₃ v words₃ (by rw [ptr₃]; exact dataFit) writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (State.addr (s.gpr .r1)) (pack v) := by rw [h₄.mem, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.rd.trans (keep₂₃.rd.trans h₁.2.1)
  have wr₄ : s₄.wr = s.wr := h₄.wr.trans (keep₂₃.wr.trans h₁.2.2.1)
  have regs₄ (r : Reg) (hr : r ∉ roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.reg r (by
      simp only [List.mem_singleton]
      intro he; subst r; exact hr (by decide)), keep₂₃.reg r hr, h₁.1]
  have scratchRead₄ : ∀ i ∈ List.range 8,
      InRegions (s₄.rd ++ s₄.wr) (State.addr (s₄.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [rd₄, wr₄, regs₄ .r2 (by decide), hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨State.addr (s.gpr .r2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have saved₄ : ∀ i ∈ List.range 8,
      s₄.mem.readW (State.addr (s₄.gpr .r2) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (blockSavedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [mem₄, regs₄ .r2 (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _))
      (by decide), h₁.2.2.2]
    exact saveMem_read _ _ _ 8 (by decide) i bound
  apply WP.mono (restoreCode_ok s₄ .r2 blockSavedReg (List.range 8) s.gpr
    (by rw [regs₄ .r2 (by decide)]; exact scratchFit)
    (fun i hi => by have := List.mem_range.mp hi; omega)
    (by decide) scratchRead₄ saved₄)
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (State.addr (s.gpr .r1)) (pack v) := h₅.2.mem.trans mem₄
  constructor
  · intro r hr
    by_cases hm : r ∈ (List.range 8).map blockSavedReg
    · exact h₅.1 r hm
    · rw [h₅.2.reg _ hm]
      have covered : ∀ r ∈ preserved,
          r ∈ (List.range 8).map blockSavedReg ∨ r ∉ roundWrites := by decide
      exact regs₄ r ((covered r hr).resolve_left hm)
  · change Spec.Rc2.blockAt s₅.mem (State.addr (s.gpr .r1)) = _
    rw [finalMem, blockAt_write64, cipher_rounds]

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 := by
  simp [PublicRegs]

theorem encrypt_verified :
    Verified target encryptBlock (Spec.Rc2.encryptBlockContract abi) := by
  refine Verified.of_correct encrypt_correct (encryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val,
    blockContract, publicRegs_three, cipher, State.addr] [satState] using satState

theorem decrypt_verified :
    Verified target decryptBlock (Spec.Rc2.decryptBlockContract abi) := by
  refine Verified.of_correct decrypt_correct (decryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val,
    blockContract, publicRegs_three, cipher, State.addr] [satState] using satState

end VG.Proof.Rc2.Arm

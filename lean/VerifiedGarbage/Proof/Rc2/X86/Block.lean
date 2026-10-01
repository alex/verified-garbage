import VerifiedGarbage.Proof.Rc2.X86.BlockCorrect
import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def blockTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 16 }

theorem blockTaint_wf {d : Spec.Rc2.Direction} {s : State} (h : (blockContract d).pre s) : VG.X86.Taint.Wf blockTaint s := by
  obtain ⟨_, wr, _, _, ao, asc, ro, rsc, _, _, _, spfit⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [blockTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (n := 12) (by omega) ro ao
  · exact Taint.frame_disjoint (n := 12) (by omega) rsc asc

theorem blockTaint_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h₁ : (blockContract d).pre s₁) (h₂ : (blockContract d).pre s₂)
    (hp : (blockContract d).pub s₁ s₂) : VG.X86.Taint.Agree blockTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (blockContract d).pre s → (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    blockTaint_wf h₁, blockTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [blockTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [blockTaint] at hk
    rw [show Taint.depth blockTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem encryptBlock_constantTime : ConstantTime isa (blockContract .encrypt).pre (blockContract .encrypt).pub encryptBlock := by
  exact VG.Taint.constantTime (A := taint) blockTaint (fun _ _ h₁ h₂ hp => blockTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlock_constantTime : ConstantTime isa (blockContract .decrypt).pre (blockContract .decrypt).pub decryptBlock := by
  exact VG.Taint.constantTime (A := taint) blockTaint (fun _ _ h₁ h₂ hp => blockTaint_agree h₁ h₂ hp)
    (by taint_decide)

def blockSatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x400d then 0x30 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_verified : Verified target encryptBlock (Spec.Rc2.encryptBlockContract abi) := by
  refine Verified.of_correct (block_correct .encrypt) encryptBlock_constantTime ?_
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · sig_implies_pre [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, blockContract, cipher]
  · intro s s' _ h
    sig_post [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal, argBytes]
    exact h.2
  · sig_implies_pub [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, blockContract, cipher]
  · sig_implies_sat [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, blockContract, cipher]
      [blockSatState, arg, argAddr, Mem.readW, Mem.read] using blockSatState

theorem decrypt_verified : Verified target decryptBlock (Spec.Rc2.decryptBlockContract abi) := by
  refine Verified.of_correct (block_correct .decrypt) decryptBlock_constantTime ?_
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · sig_implies_pre [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, blockContract, cipher]
  · intro s s' _ h
    sig_post [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal, argBytes]
    exact h.2
  · sig_implies_pub [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, blockContract, cipher]
  · sig_implies_sat [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, blockContract, cipher]
      [blockSatState, arg, argAddr, Mem.readW, Mem.read] using blockSatState

end VG.Proof.Rc2.X86

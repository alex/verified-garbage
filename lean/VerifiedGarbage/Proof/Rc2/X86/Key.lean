import VerifiedGarbage.Proof.Rc2.X86.KeyCorrect
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rc2.X86.KeyLit

/-! # RC2 key expansion against the shared API contract -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def keyTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem keyTaint_wf {s : State} (h : keyContract.pre s) : VG.X86.Taint.Wf keyTaint s := by
  obtain ⟨_, wr, _, _, _, ao, asc, ro, rsc, _, _, _, spfit, _⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [keyTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (n := 20) (by omega) ro ao
  · exact Taint.frame_disjoint (n := 20) (by omega) rsc asc

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : keyContract.pre s₁) (h₂ : keyContract.pre s₂)
    (hp : keyContract.pub s₁ s₂) : VG.X86.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, keyContract.pre s → (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    keyTaint_wf h₁, keyTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [keyTaint] at hk
    rw [show Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem expandKey_constantTime : ConstantTime isa keyContract.pre keyContract.pub expandKey := by
  exact VG.Taint.constantTime (A := taint) keyTaint (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

def keySatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 1 else
    if a = 0x400c then 8 else if a = 0x4011 then 0x20 else if a = 0x4015 then 0x30 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x4004, 20⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct key_body_correct expandKey_constantTime ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argSlots, argVal,
    argBytes, addr32, keyContract, Spec.Rc2.validKey]
    [keySatState, arg, argAddr, Mem.readW, Mem.read] using keySatState

end VG.Proof.Rc2.X86

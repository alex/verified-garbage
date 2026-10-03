import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Spec.Rc4.Contract

/-!
# RC4 on x86 (32-bit): the contracts the proofs use

`Spec.Rc4.initContract` and `Spec.Rc4.applyContract` spelled out for x86,
with the arguments only read (the taint analysis follows them in memory only
while nothing that may alias them is written): `initC` and `applyC`.
`wideInit` and `wideApply` let the code write them, as the shared contracts
do, and imply those; `Verified.lean` narrows them back.
-/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Spec.Rc4

def initC : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let ctx : Region := ⟨(arg s 2).setWidth 64, 258⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [ctx, scratch] ∧ key.Disjoint ctx ∧ key.Disjoint scratch ∧
      ctx.Disjoint scratch ∧ args.Disjoint ctx ∧ args.Disjoint scratch ∧ ret.Disjoint ctx ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 258 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    match init (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) with
    | .ok c => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
        contextAt s'.mem ((arg s 2).setWidth 64) = c
    | .error .invalidKeyLength => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

def applyC : Contract isa where
  pre s :=
    let ctx : Region := ⟨(arg s 0).setWidth 64, 258⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [ctx, data, scratch] ∧ ctx.Disjoint data ∧ ctx.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint ctx ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
      ret.Disjoint ctx ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 258 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    let result := update (contextAt s.mem ((arg s 0).setWidth 64))
      (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
    contextAt s'.mem ((arg s 0).setWidth 64) = result.1 ∧
      bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat = result.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 4, arg s₁ i = arg s₂ i) ∧
    [(contextAt s₁.mem ((arg s₁ 0).setWidth 64)).i.toNat] =
      [(contextAt s₂.mem ((arg s₂ 0).setWidth 64)).i.toNat]

/-- `initC`, with the arguments writable. -/
def wideInit : Contract isa :=
  { initC with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
      let ctx : Region := ⟨(arg s 2).setWidth 64, 258⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [key] ∧ s.wr = [ctx, scratch, args] ∧ key.Disjoint ctx ∧ key.Disjoint scratch ∧
        ctx.Disjoint scratch ∧ args.Disjoint ctx ∧ args.Disjoint scratch ∧ ret.Disjoint ctx ∧
        ret.Disjoint scratch ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
        (arg s 2).toNat + 258 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
        (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

/-- `applyC`, with the arguments writable. -/
def wideApply : Contract isa :=
  { applyC with
    pre := fun s =>
      let ctx : Region := ⟨(arg s 0).setWidth 64, 258⟩
      let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [] ∧ s.wr = [ctx, data, scratch, args] ∧ ctx.Disjoint data ∧
        ctx.Disjoint scratch ∧ data.Disjoint scratch ∧ args.Disjoint ctx ∧ args.Disjoint data ∧
        args.Disjoint scratch ∧ ret.Disjoint ctx ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
        (arg s 0).toNat + 258 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
        (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

/-- `init(0x1000, 1, 0x2000, 0x3000)`. -/
def initSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 1 else if a = 0x600d then 0x20 else
    if a = 0x6011 then 0x30 else 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩, ⟨0x3000, 64⟩, ⟨0x6004, 16⟩]

/-- `apply(0x1000, 0x2000, 1, 0x3000)`. -/
def applySat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6009 then 0x20 else if a = 0x600c then 1 else
    if a = 0x6011 then 0x30 else 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩, ⟨0x3000, 64⟩, ⟨0x6004, 16⟩]

syntax "wide_pre " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wide_pre [$ls,*]) => `(tactic| (
    intro s h
    sig_pre [$ls,*] at h
    sig_split h
    sig_reduce [$ls,*]
    sig_simp [$ls,*] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega))

theorem init_implies : wideInit.Implies (initContract abi) where
  pre := by
    wide_pre [initContract, initSig, abi, argSlots, argVal, argBytes, wideInit, initC]
  post := by
    sig_implies_post [initContract, initSig, abi, argSlots, argVal, argBytes, wideInit, initC]
  pub := by
    sig_implies_pub [initContract, initSig, abi, argSlots, argVal, argBytes, wideInit, initC]
  sat := by
    sig_implies_sat [initContract, initSig, abi, argSlots, argVal, argBytes, wideInit, initC]
      [initSat, arg, argAddr, Mem.readW, Mem.read] using initSat

theorem apply_implies : wideApply.Implies (applyContract abi) where
  pre := by
    wide_pre [applyContract, applySig, abi, argSlots, argVal, argBytes, wideApply, applyC]
  post := by
    sig_implies_post [applyContract, applySig, abi, argSlots, argVal, argBytes, wideApply, applyC]
  pub := by
    sig_implies_pub [applyContract, applySig, abi, argSlots, argVal, argBytes, wideApply, applyC]
  sat := by
    sig_implies_sat [applyContract, applySig, abi, argSlots, argVal, argBytes, wideApply, applyC]
      [applySat, arg, argAddr, Mem.readW, Mem.read] using applySat

end VG.Proof.Rc4.X86

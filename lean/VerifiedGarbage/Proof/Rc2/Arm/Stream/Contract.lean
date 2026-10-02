import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming RC2-CBC on ARMv7: the contracts, spelled out

Untrusted: everything here is checked by Lean. The contracts of
`vg_rc2_cbc_init` and the update functions with their facts written out for
ARMv7 and a stack of 8 bytes (`initContract`, `updateContract`), which imply
the shared ones (`init_implies`, `update_implies`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let iv : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let ctx : Region := ⟨State.addr (stackArg s 1), 144⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 576⟩
    let below : Region := ⟨State.addr s.sp - 8, 8⟩
    8 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧ s.rd = [key, iv, args] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
      ctx.Disjoint args ∧ scr.Disjoint args ∧ below.Disjoint key ∧ below.Disjoint iv ∧
      below.Disjoint ctx ∧ below.Disjoint scr ∧ below.Disjoint args ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 144 ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
        (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) direction
        (s.gpr .r2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.Rc2.contextAt s'.mem (State.addr (stackArg s 1)) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = e.code
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 144⟩
    let data : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let out : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 576⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let below : Region := ⟨State.addr s.sp - 8, 8⟩
    8 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧ s.rd = [data, args] ∧ s.wr = [ctx, out, scr] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧
      data.Disjoint out ∧ data.Disjoint scr ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      scr.Disjoint args ∧ below.Disjoint ctx ∧ below.Disjoint data ∧ below.Disjoint out ∧
      below.Disjoint scr ∧ below.Disjoint args ∧
      (s.gpr .r0).toNat + 144 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat < 8 ∧ (stackArg s 1).toNat = ((s.gpr .r1).toNat + (s.gpr .r3).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (State.addr (s.gpr .r0)) d (s.gpr .r1).toNat)
      (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    Spec.Rc2.contextAt s'.mem (State.addr (s.gpr .r0)) d (((s.gpr .r1).toNat + (s.gpr .r3).toNat) % 8) =
        result.1 ∧
      Spec.Rc2.bytesAt s'.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat = result.2
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def initSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r3 => 0x2000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6005 then 0x30 else if a = 0x6009 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 12⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

def updateSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x30 else if a = 0x6009 then 0x40 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x6000, 12⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

theorem init_implies : initContract.Implies (Spec.Rc2.cbcInitContract abi 8) := by
  sig_implies [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, initContract]
    [initSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using initSatState

theorem update_implies (d : Spec.Rc2.Direction) :
    (updateContract d).Implies (Spec.Rc2.cbcUpdateContract abi d 8) := by
  sig_implies [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, updateContract]
    [updateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using updateSatState

end VG.Proof.Rc2.Arm.Stream

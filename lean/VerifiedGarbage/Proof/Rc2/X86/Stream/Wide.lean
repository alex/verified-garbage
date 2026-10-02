import VerifiedGarbage.Proof.Rc2.X86.Stream.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# Streaming RC2-CBC on x86 (32-bit): the shared contracts

The shared contracts (`Spec.Rc2.cbcInitContract`,
`Spec.Rc2.cbcUpdateContract`) let the code write its arguments; `wideInit` and
`wideUpdate` are the per-target contracts with that permission, which imply
the shared ones. `narrow*` drop it again, for the proofs against
`initContract` and `updateContract`.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- `initContract`, with the arguments writable. -/
def wideInit : Contract isa :=
  { initContract with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
      let iv : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let ctx : Region := ⟨(arg s 5).setWidth 64, 144⟩
      let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 28⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 24
      s.rd = [key, iv] ∧ s.wr = [ctx, buf, args] ∧
        key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
        args.Disjoint ctx ∧ args.Disjoint buf ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧
        stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧
        (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
        (arg s 5).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
        24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 }

/-- `updateContract d`, with the arguments writable. -/
def wideUpdate (d : Spec.Rc2.Direction) : Contract isa :=
  { updateContract d with
    pre := fun s =>
      let ctx : Region := ⟨(arg s 0).setWidth 64, 144⟩
      let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
      let out : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
      let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 28⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 40
      s.rd = [data] ∧ s.wr = [ctx, out, buf, args] ∧
        ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ data.Disjoint out ∧
        data.Disjoint buf ∧ out.Disjoint buf ∧
        args.Disjoint ctx ∧ args.Disjoint out ∧ args.Disjoint buf ∧
        ret.Disjoint ctx ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧
        stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧
        (arg s 0).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
        (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
        40 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
        (arg s 1).toNat < 8 ∧ (arg s 5).toNat = ((arg s 1).toNat + (arg s 3).toNat) / 8 * 8 }

/-- `init(0x1000, 1, 8, 0x2000, 8, 0x3000, 0x4000)`. -/
def initSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 1 else if a = 0x600c then 8 else
    if a = 0x6011 then 0x20 else if a = 0x6014 then 8 else if a = 0x6019 then 0x30 else
    if a = 0x601d then 0x40 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩, ⟨0x6004, 28⟩]

/-- `update(0x1000, 0, 0x2000, 0, 0x3000, 0, 0x4000)`. -/
def updateSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x600d then 0x20 else if a = 0x6015 then 0x30 else
    if a = 0x601d then 0x40 else 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩, ⟨0x6004, 28⟩]

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
      | omega
      | (rw [Taint.sub_setWidth (by omega)]
         first
           | with_reducible assumption
           | with_reducible exact Region.Disjoint.symm ‹_›)))

theorem init_implies : wideInit.Implies (Spec.Rc2.cbcInitContract abi 24) where
  pre := by
    wide_pre [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  post := by
    sig_implies_post [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  pub := by
    sig_implies_pub [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  sat := by
    sig_implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below] [initSat, arg, argAddr, Mem.readW, Mem.read] using initSat

theorem update_implies (d : Spec.Rc2.Direction) :
    (wideUpdate d).Implies (Spec.Rc2.cbcUpdateContract abi d 40) where
  pre := by
    wide_pre [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below]
  post := by
    sig_implies_post [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below]
  pub := by
    sig_implies_pub [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below]
  sat := by
    sig_implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below] [updateSat, arg, argAddr, Mem.readW, Mem.read] using updateSat

end VG.Proof.Rc2.X86.Stream

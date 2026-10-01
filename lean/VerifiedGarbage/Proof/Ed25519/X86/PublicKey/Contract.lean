import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Layout
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86

def pkWide : Contract isa := { pkLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
}

def pkSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def pkSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pkSatMem
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem pkWide_pre (s : State) (h : pkWide.pre s) :
    pkLocal.pre (s.withRegions (pkRd s) (pkWr s)) := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩ := h
  simp only [pkLocal, pkRd, pkWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, below, Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩

theorem pkWide_implies : pkWide.Implies (Spec.Ed25519.publicKeyContract X86.abi 280) := by
  have a0 : arg pkSatState 0 = 0x1000 := by decide
  have a1 : arg pkSatState 1 = 0x2000 := by decide
  have a2 : arg pkSatState 2 = 0x4000 := by decide
  have e : argAddr pkSatState 0 = 0x8004 := by decide
  have sp : pkSatState.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, pkWide, pkLocal, below, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, e, sp] using pkSatState

end VG.Proof.Ed25519.X86.PublicKey

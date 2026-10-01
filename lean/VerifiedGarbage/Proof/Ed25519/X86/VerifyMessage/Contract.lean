import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Entry
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

def verifyWide : Contract isa := { verifyMessageLocal with
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let sig : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [pk, msg, sig] ∧ s.wr = [scr, args] ∧
      pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

theorem verifyWide_pre (s : State) (h : verifyWide.pre s) :
    verifyMessageLocal.pre (s.withRegions (verifyRd s) (verifyWr s)) := by
  simp only [verifyMessageLocal, verifyRd, verifyWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

def verifySatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else
    if a = 0x800c then 0x40 else if a = 0x8011 then 0x30 else if a = 0x8015 then 0x40 else 0

def verifySatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := verifySatMem
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8004, 20⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verifyWide_implies : verifyWide.Implies (Spec.Ed25519.verifyContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, verifyWide, verifyMessageLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = signWord _ at h
    rw [h, BitVec.setWidth_append_eq_right]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
      (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last⟩
  sat := by
    have a0 : arg verifySatState 0 = 0x1000 := by decide
    have a1 : arg verifySatState 1 = 0x2000 := by decide
    have a2 : arg verifySatState 2 = 64 := by decide
    have a3 : arg verifySatState 3 = 0x3000 := by decide
    have a4 : arg verifySatState 4 = 0x4000 := by decide
    have e : argAddr verifySatState 0 = 0x8004 := by decide
    have esp : verifySatState.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, verifyWide, verifyMessageLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, e, esp] using verifySatState

end VG.Proof.Ed25519.X86.VerifyMessage

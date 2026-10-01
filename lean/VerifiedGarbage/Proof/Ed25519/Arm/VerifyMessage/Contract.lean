import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Entry
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Equation
import VerifiedGarbage.Proof.Framework.Arm.Contract

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 64 | .r3 => 0x3000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9001 then 0x40 else 0
  rd := [⟨0x1000,32⟩,⟨0x2000,64⟩,⟨0x3000,64⟩,⟨0x9000,4⟩]
  wr := [⟨0x4000,8192⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

private theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

private theorem pre_bridge (s : State) (h : (Spec.Ed25519.verifyContract Arm.abi 280).pre s) :
    verifyMessageLocal.pre s := by
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  sig_split h
  sig_reduce [verifyMessageLocal, Arm.State.addr]
  sig_simp [argAddr_zero, Arm.State.addr] [] at *
  simp only [Arm.State.addr, show (280#64) = (280 : Addr) from rfl] at *
  sig_and_intros
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem verifyMessage_implies : verifyMessageLocal.Implies (Spec.Ed25519.verifyContract Arm.abi 280) where
  pre := pre_bridge
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Arm.abi,Arm.argRegs,Arm.reduceClassify,Arm.Loc.val,Arm.State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Arm.abi,Arm.argRegs,Arm.reduceClassify,Arm.Loc.val,Arm.State.addr] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last⟩
  sat := by
    refine ⟨verifySatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
        Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, verifySatState]
      decide +kernel


end VG.Proof.Ed25519.Arm.VerifyMessage

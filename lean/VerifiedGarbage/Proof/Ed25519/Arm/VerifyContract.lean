import VerifiedGarbage.Proof.Ed25519.Arm.VerifyStoreHeaders
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.TCB.Arm.Target

/-! Untrusted local contract for the four-register verification ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def verifyLocal : Contract Arm.isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let sig : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let challenge : Region := ⟨State.addr (s.gpr .r2), 64⟩
    let ws : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [pk, sig, challenge] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧
      challenge.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s t := (t.gpr .r0).toNat = if Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32 ++
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 ++
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r0)) 32 ++
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r1)) 64 ++
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r2)) 64).map (·.toNat)

structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r1), 64⟩, ⟨State.addr (s.gpr .r2), 64⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r3), 8192⟩]
  pk_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  sig_ws : (⟨State.addr (s.gpr .r1), 64⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  challenge_ws : (⟨State.addr (s.gpr .r2), 64⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 64 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

theorem VerifyPre.of {s : State} (h : verifyLocal.pre s) : VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end VG.Proof.Ed25519.Arm

import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMain
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom

/-! Untrusted: verifier inputs are public and unchanged throughout the computation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure VerifyPublic (m : Mem) (b pk sig challenge : BitVec 32) (s : State) : Prop where
  ctx : VerifyContext b pk sig challenge s
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem VerifyPublic.keep {m : Mem} {b pk sig challenge : BitVec 32} {s t : State}
    (h : VerifyPublic m b pk sig challenge s) (hk : VerifyKeep b s t) : VerifyPublic m b pk sig challenge t :=
  ⟨h.ctx.keep hk, (h.ctx.pkInput.bytes hk).trans h.pkBytes,
    (h.ctx.sigInput.bytes hk).trans h.sigBytes, (h.ctx.challengeInput.bytes hk).trans h.challengeBytes⟩

theorem VerifyPublic.rBytes {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr sig) 32 = Spec.Ed25519.bytesAt m (State.addr sig) 32 := by
  have he := congrArg (List.take 32) h.sigBytes
  simpa only [signatureBytes_take] using he

theorem VerifyPublic.sBytes {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) :
    Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32 = Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32 := by
  have ep : State.addr (sig + (32 : BitVec 32)) = State.addr sig + BitVec.ofNat 64 32 :=
    addr_add (k := 32) (by have := h.ctx.sigInput.fit; omega)
  rw [ep]
  have he := congrArg (List.drop 32) h.sigBytes
  simpa only [signatureBytes_drop] using he

theorem VerifyPublic.eqResult {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) (a r : Spec.Ed25519.Point) :
    equationResult s.mem sig challenge a r = equationResult m sig challenge a r := by
  unfold equationResult
  rw [h.sBytes, h.challengeBytes]

theorem VerifyPublic.withR {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) (a : Spec.Ed25519.Point) :
    equationWithR s.mem sig challenge a = equationWithR m sig challenge a := by
  unfold equationWithR
  rw [h.rBytes]
  split
  · rfl
  · exact h.eqResult _ _

theorem VerifyPublic.decoded {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) : decodedEquation s.mem pk sig challenge = decodedEquation m pk sig challenge := by
  unfold decodedEquation
  rw [h.pkBytes]
  split
  · rfl
  · exact h.withR _

end VG.Proof.Ed25519.Arm

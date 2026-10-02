import VerifiedGarbage.Proof.Ed25519.Arm.VerifyDecodeA
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyScalar
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

/-! The complete verifier body implements the reviewed strict equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : BitVec 32) (hs : sig.toNat + 64 ≤ 2 ^ 32) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m (State.addr pk) 32)
      (Spec.Ed25519.bytesAt m (State.addr sig) 64) (Spec.Ed25519.bytesAt m (State.addr challenge) 64) =
      (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L) &&
        decodedEquation m pk sig challenge) := by
  have ep : State.addr (sig + (32 : BitVec 32)) = State.addr sig + BitVec.ofNat 64 32 := addr_add (k := 32) (by omega)
  rw [Spec.Ed25519.verifyEquation]
  simp only [bytesAt_length, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false,
    signatureBytes_take, signatureBytes_drop, ← ep]
  unfold decodedEquation equationWithR equationResult
  cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32) <;>
    cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32) <;>
    simp only [Bool.and_false]

theorem verifyBody_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) :
    WP isa verifyBody s fun t => VerifyKeep b s t ∧ t.gpr .r9 = BitVec.ofNat 32
      (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32)
        (Spec.Ed25519.bytesAt s.mem (State.addr sig) 64) (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)).toNat := by
  refine WP.seq (WP.mono (verifyScalar_ok hc) fun u ⟨uk, uz⟩ => ?_)
  apply WP.ite _ (congrArg some uz)
  · intro hy
    refine WP.seq (WP.mono (initFields_ok (uk.ctx hc.ctx)) fun v ⟨vk, vl, _⟩ => ?_)
    have kv := uk.trans (VerifyKeep.of_keep vk)
    refine WP.mono (verifyDecodeA_ok (hc.keep kv) vl) fun t ⟨tk, tv⟩ => ?_
    refine ⟨kv.trans tk, ?_⟩
    rw [decodedEquation_keep hc kv] at tv
    rw [verifyEquation_bytes _ _ _ _ hc.sigInput.fit, hy, Bool.true_and]
    exact tv
  · intro hn
    refine WP.mono (recoverInvalid_ok u b) fun t ⟨tk, _, tv⟩ => ?_
    refine ⟨uk.trans (VerifyKeep.of_keep tk), ?_⟩
    rw [verifyEquation_bytes _ _ _ _ hc.sigInput.fit, hn, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.Arm

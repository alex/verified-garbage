import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyDecodeA
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

/-! The strict scalar check and decoding branches implement verifyEquation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

private theorem decodedEquation_order (a r : Option Spec.Ed25519.Point) (s k : Nat) :
    (match a, r with
      | some a, some r => decide (s < Spec.Ed25519.L) &&
          Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))
      | _, _ => false) = (decide (s < Spec.Ed25519.L) && decodedEquation a r s k) := by
  cases a <;> cases r <;> simp only [decodedEquation, equationWithR, Bool.and_false]

private theorem verifyEquation_order (pk sig challenge : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : challenge.length = 64) :
    Spec.Ed25519.verifyEquation pk sig challenge =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        decodedEquation (Spec.Ed25519.decodePoint pk) (Spec.Ed25519.decodePoint (sig.take 32))
          (Spec.Ed25519.decodeLE (sig.drop 32)) (Spec.Ed25519.decodeLE challenge)) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  exact decodedEquation_order _ _ _ _

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : Addr) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m pk 32)
      (Spec.Ed25519.bytesAt m sig 64) (Spec.Ed25519.bytesAt m challenge 64) =
    (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32) < Spec.Ed25519.L) &&
      decodedEquation (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m challenge 64))) := by
  rw [verifyEquation_order _ _ _ (bytesAt_length ..) (bytesAt_length ..) (bytesAt_length ..),
    signatureBytes_take, signatureBytes_drop]

theorem verifyBody_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld dbl) recoverInvalid)) s fun t =>
      VerifyKeep base s t ∧ t.gpr .rax = signWord
        (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem pk 32)
          (Spec.Ed25519.bytesAt s.mem sig 64) (Spec.Ed25519.bytesAt s.mem challenge 64)) := by
  refine WP.seq (WP.mono (verifyScalar_ok h.scratch h.sigHeader h.scalarRead) fun a ⟨ka, am, ac⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keep ka
  apply WP.ite _ ac
  · intro ht
    refine WP.mono (verifyDecodeA_ok (h.of_keep kap)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans kt, ?_⟩
    rw [am] at tv
    rw [verifyEquation_bytes, ht, Bool.true_and]
    exact tv
  · intro hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans (PowersKeep.of_keep kt), ?_⟩
    rw [verifyEquation_bytes, hf, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.X86_64

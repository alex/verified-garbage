import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed25519.X86.VerifyScalar
import VerifiedGarbage.Proof.Ed25519.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verificationScalar_num {s : State} (hp : VerifyPre s) :
    verificationScalar s = fe s.mem (arg s 1 + 32) 0 := by
  rw [verificationScalar, ← addr_zero (arg s 1 + BitVec.ofNat 32 32)]
  exact decode_words s.mem 8 (by have := hp.scalar.fit; omega_using [this])

private theorem verification_order (pk sig ch : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : ch.length = 64) :
    Spec.Ed25519.verifyEquation pk sig ch =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        (match Spec.Ed25519.decodePoint pk with
        | none => false
        | some a => match Spec.Ed25519.decodePoint (sig.take 32) with
          | none => false
          | some r => Spec.Ed25519.pointEqual
            (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (sig.drop 32)) Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE ch) a)))) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  cases Spec.Ed25519.decodePoint pk <;> cases Spec.Ed25519.decodePoint (sig.take 32) <;>
    simp only [Bool.and_false]

theorem verifyEquation_result {s : State} (hp : VerifyPre s) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64) =
      (decide (verificationScalar s < Spec.Ed25519.L) && decodeResult s) := by
  have address : (arg s 1 + BitVec.ofNat 32 32).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 32 :=
    addr_eq (by have hf := hp.signature_fit; omega_using [hf])
  rw [verification_order _ _ _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]),
    signatureBytes_take, signatureBytes_drop, ← address]
  have zero (i : Nat) : arg s i + BitVec.ofNat 32 0 = arg s i := BitVec.add_zero _
  simp only [decodeResult, decodeRResult, inputPoint, equationResult, verificationScalar,
    verificationChallenge, zero]
  cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32) <;>
    cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) <;> rfl

theorem verifyBody_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid)) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
        (decide (verificationScalar s₀ < Spec.Ed25519.L) && decodeResult s₀) := by
  refine WP.seq (WP.mono (verifyScalar_ok hp.scratch hp.scalar hs) fun a ⟨ha, za⟩ => ?_)
  rw [← verificationScalar_num hp] at za
  apply WP.ite (decide (verificationScalar s₀ < Spec.Ed25519.L)) za
  · intro hh
    refine WP.mono (verifyDecodeA_ok hp ha) fun t ⟨ht, vt⟩ => ⟨ht, ?_⟩
    rw [hh, Bool.true_and]
    exact vt
  · intro hh
    refine WP.mono (recoverInvalid_ok a (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨ha.ikeep hp.scratch.fit (IKeep.of_field kt), by rw [hh, Bool.false_and]; exact rt⟩

theorem verify_correct {s : State} (h : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  have hp := verify_pre h
  refine WP.seq (WP.mono (abiSave_ok hp.scratch) fun a ha => ?_)
  refine WP.seq (WP.mono (verifyBody_ok hp ha) fun b ⟨hb, vb⟩ => ?_)
  refine WP.mono (verifyFinish_ok hp.scratch hb) fun t ⟨abi_t, vt, _⟩ => ⟨abi_t, ?_⟩
  change t.gpr .eax = _
  rw [vt, vb, verifyEquation_result hp]

end VG.Proof.Ed25519.X86

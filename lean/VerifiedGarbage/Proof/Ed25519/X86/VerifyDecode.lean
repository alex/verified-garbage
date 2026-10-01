import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecodeInput
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def equationResult (s : State) (a r : Spec.Ed25519.Point) : Bool :=
  Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul (verificationScalar s) Spec.Ed25519.basePoint)
    (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (verificationChallenge s) a))

def decodeRResult (s : State) (a : Spec.Ed25519.Point) : Bool :=
  match inputPoint s 1 with | none => false | some r => equationResult s a r

def decodeResult (s : State) : Bool :=
  match inputPoint s 0 with | none => false | some a => decodeRResult s a

theorem verifyDecodeR_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa verifyDecodeR s fun t => Saved s₀ (arg s₀ 3) t ∧
      t.gpr .eax = signWord (decodeRResult s₀ (tablePoint s.mem (arg s₀ 3) 7680)) := by
  apply WP.assoc
  refine WP.seq (WP.mono (decodeInput_ok hp.scratch hp.r hs (by decide)) fun a ht => ?_)
  have ha := ht.1
  have fa := ht.2.1
  with_reducible apply decodedThen_ok ha ht.2.2
  · intro b hb _ hn
    refine WP.mono (recoverInvalid_ok b (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨hb.ikeep hp.scratch.fit (IKeep.of_field kt), by
      rw [decodeRResult, hn]
      change t.gpr .eax = 0
      exact rt⟩
  · intro b r hb mb hr pb
    refine WP.seq (WP.mono (pointTableWrite_ok (hb.ctx hp.scratch.fit hp.scratch.wr) 7808 (by decide) (by decide))
      fun c ⟨kc, fc, pc⟩ => ?_)
    have hc := hb.of_offset hp.scratch.fit kc fc (by decide) (by decide) (by decide)
    refine WP.mono (verifyEquationPoints_ok hp hc) fun t ⟨ht, vt⟩ => ?_
    have ca : tablePoint c.mem (arg s₀ 3) 7680 = tablePoint s.mem (arg s₀ 3) 7680 := by
      rw [tablePoint_frame hp.scratch.fit fc (by decide) (by decide) (Or.inl (by decide)), mb,
        tablePoint_frame hp.scratch.fit fa (by decide) (by decide) (Or.inr (by decide))]
    refine ⟨ht, ?_⟩
    rw [vt, pc, pb, ca]
    simp only [decodeRResult, hr, equationResult]

theorem verifyDecodeA_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa verifyDecodeA s fun t => Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord (decodeResult s₀) := by
  apply WP.assoc
  refine WP.seq (WP.mono (decodeInput_ok hp.scratch hp.pk hs (by decide)) fun a ht => ?_)
  have ha := ht.1
  with_reducible apply decodedThen_ok ha ht.2.2
  · intro b hb _ hn
    refine WP.mono (recoverInvalid_ok b (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨hb.ikeep hp.scratch.fit (IKeep.of_field kt), by
      rw [decodeResult, hn]
      change t.gpr .eax = 0
      exact rt⟩
  · intro b p hb _ hr pb
    refine WP.seq (WP.mono (pointTableWrite_ok (hb.ctx hp.scratch.fit hp.scratch.wr) 7680 (by decide) (by decide))
      fun c ⟨kc, fc, pc⟩ => ?_)
    have hc := hb.of_offset hp.scratch.fit kc fc (by decide) (by decide) (by decide)
    refine WP.mono (verifyDecodeR_ok hp hc) fun t ⟨ht, vt⟩ => ?_
    exact ⟨ht, by rw [vt, pc, pb]; simp only [decodeResult, hr]⟩

end VG.Proof.Ed25519.X86

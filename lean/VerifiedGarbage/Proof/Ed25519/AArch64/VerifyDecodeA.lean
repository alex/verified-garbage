import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyDecodeR

/-! Untrusted: reject an invalid public key encoding before computing the equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def decodedEquation (a r : Option Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match a with
  | none => false
  | some a => equationWithR r a scalar challenge

theorem verifyDecodeA_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa verifyDecodeA s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (decodedEquation
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeA]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .x2 7936 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (base := base) (p := pk) ha.scratch (ap.trans h.pkHeader) ha.pkRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem pk 32) = decoded at hd
  rw [ka.mem] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c p kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, decodedEquation, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7424 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    refine WP.mono (verifyDecodeR_ok (h.of_keep kabcd)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, verifyKeep_bytes kabcd h.rFar, verifyKeep_bytes kabcd h.scalarFar,
      verifyKeep_bytes kabcd h.challengeFar, hp, hy, decodedEquation]

end VG.Proof.Ed25519.AArch64

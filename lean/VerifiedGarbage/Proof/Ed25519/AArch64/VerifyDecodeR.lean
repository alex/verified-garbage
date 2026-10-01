import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext

/-! Untrusted: reject an invalid R encoding or evaluate the complete equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def equationWithR (r : Option Spec.Ed25519.Point) (a : Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match r with
  | none => false
  | some r => Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul challenge a))

theorem verifyDecodeR_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa verifyDecodeR s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (equationWithR
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (tablePoint s.mem base 7424)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeR]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .x2 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (base := base) (p := sig) ha.scratch (ap.trans h.sigHeader) ha.rRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem sig 32) = decoded at hd
  rw [ka.mem] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c r kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, equationWithR, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7552 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    have hd := h.of_keep kabcd
    have da : tablePoint d.mem base 7424 = tablePoint s.mem base 7424 := by
      rw [kd.mem.point (by decide) (Or.inl (by decide)) (by decide), kc.mem,
        workspace_tablePoint kb.mem (by decide) (by decide), ka.mem]
    refine WP.mono (verifyEquationPoints_ok hd.scratch hd.sigHeader hd.challengeHeader
      hd.scalarBytes hd.scalarFar hd.challengeRead hd.challengeWords hd.challengeFar) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, da, verifyKeep_bytes kabcd h.scalarFar, verifyKeep_bytes kabcd h.challengeFar,
      hp, hy, equationWithR]

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Ed25519.Arm.VerifyDecodeR

/-! Both public points use the strict decoder. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def decodedEquation (m : Mem) (pk sig challenge : BitVec 32) : Bool :=
  match Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32) with
  | none => false
  | some a => equationWithR m sig challenge a

theorem equationWithR_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) (a : Spec.Ed25519.Point) :
    equationWithR t.mem sig challenge a = equationWithR s.mem sig challenge a := by
  unfold equationWithR
  rw [(hc.sigInput.prefix (n := 32) (by decide)).bytes hk]
  split
  · rfl
  · exact equationResult_keep hc hk _ _

theorem decodedEquation_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) :
    decodedEquation t.mem pk sig challenge = decodedEquation s.mem pk sig challenge := by
  unfold decodedEquation
  rw [hc.pkInput.bytes hk]
  split
  · rfl
  · exact equationWithR_keep hc hk _

theorem verifyDecodeA_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyDecodeA s fun t => VerifyKeep b s t ∧
      t.gpr .r9 = BitVec.ofNat 32 (decodedEquation s.mem pk sig challenge).toNat := by
  refine WP.seq (WP.mono (loadHeader_ok hc.ctx 8128 (by decide)) fun u ⟨ur, um, up⟩ => ?_)
  have ku : VerifyKeep b s u := VerifyKeep.of_rest ur (by decide) um
  have uc := hc.keep ku
  refine WP.seq (WP.mono (pointDecode_ok uc.ctx (um ▸ hl) (up.trans hc.pkHeader)
    uc.pkInput.fit uc.pkInput.readable uc.pkInput.separate) fun v hv => ?_)
  have vk := hv.1
  have vl := hv.2.1
  have kv := ku.trans (VerifyKeep.of_decode vk)
  cases dec : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr pk) 32) with
  | none =>
    have vr : v.gpr .r9 = 0 := by
      change DecodeResult b none v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) um).trans dec)) hv.2.2
    refine decodedThen_ok false vr ?_ ?_
    · intro h; exact Bool.noConfusion h
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.mono (recoverInvalid_ok w b) fun t ⟨tk, _, tv⟩ => ?_
      refine ⟨kw.trans (VerifyKeep.of_keep tk), ?_⟩
      simp only [decodedEquation, dec, Bool.toNat_false]
      exact tv
  | some a =>
    have result : v.gpr .r9 = 1 ∧ point (env v.mem b) 0 1 2 3 = a := by
      change DecodeResult b (some a) v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) um).trans dec)) hv.2.2
    rcases result with ⟨vr, vp⟩
    refine decodedThen_ok true vr ?_ ?_
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.seq (WP.mono (pointTableWrite_ok (kw.ctx hc.ctx) (wm ▸ vl) 7744 (by decide) (by decide))
        fun x ⟨xk, xl, _, xp⟩ => ?_)
      have kx := kw.trans (VerifyKeep.of_powers xk (by decide) (by decide))
      have xa : tablePoint x.mem b 7744 = a :=
        xp.trans ((congrArg (fun m => point (env m b) 0 1 2 3) wm).trans vp)
      refine WP.mono (verifyDecodeR_ok (hc.keep kx) xl) fun t ⟨tk, tv⟩ => ?_
      refine ⟨kx.trans tk, ?_⟩
      rw [xa, equationWithR_keep hc kx] at tv
      simp only [decodedEquation, dec]
      exact tv
    · intro h; exact Bool.noConfusion h

end VG.Proof.Ed25519.Arm

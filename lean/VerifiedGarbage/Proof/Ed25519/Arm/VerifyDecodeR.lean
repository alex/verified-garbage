import VerifiedGarbage.Proof.Ed25519.Arm.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.Arm.DecodedThen
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode

/-! Strict decoding of R precedes the full verification equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def equationWithR (m : Mem) (sig challenge : BitVec 32) (a : Spec.Ed25519.Point) : Bool :=
  match Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32) with
  | none => false
  | some r => equationResult m sig challenge a r

theorem equationResult_keep {b pk sig challenge : BitVec 32} {s t : State}
    (hc : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) (a r : Spec.Ed25519.Point) :
    equationResult t.mem sig challenge a r = equationResult s.mem sig challenge a r := by
  unfold equationResult
  rw [(hc.sigInput.suffix32).bytes hk, hc.challengeInput.bytes hk]

theorem DecodeKeep.table {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) {d : Nat}
    (hd : 1600 ≤ d) (hn : d + 128 ≤ 8192) : tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

theorem verifyDecodeR_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyDecodeR s fun t => VerifyKeep b s t ∧
      t.gpr .r9 = BitVec.ofNat 32 (equationWithR s.mem sig challenge (tablePoint s.mem b 7744)).toNat := by
  refine WP.seq (WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun u ⟨ur, um, up⟩ => ?_)
  have ku : VerifyKeep b s u := VerifyKeep.of_rest ur (by decide) um
  have uc := hc.keep ku
  have ui := uc.sigInput.prefix (n := 32) (by decide)
  refine WP.seq (WP.mono (pointDecode_ok uc.ctx (um ▸ hl) (up.trans hc.sigHeader)
    ui.fit ui.readable ui.separate) fun v hv => ?_)
  have vk := hv.1
  have vl := hv.2.1
  have kv := ku.trans (VerifyKeep.of_decode vk)
  have va : tablePoint v.mem b 7744 = tablePoint s.mem b 7744 :=
    (vk.table (by decide) (by decide)).trans (congrArg (fun m => tablePoint m b 7744) um)
  cases dec : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr sig) 32) with
  | none =>
    have vr : v.gpr .r9 = 0 := by
      change DecodeResult b none v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) um).trans dec)) hv.2.2
    refine decodedThen_ok false vr ?_ ?_
    · intro h; exact Bool.noConfusion h
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.mono (recoverInvalid_ok w b) fun t ⟨tk, _, tv⟩ => ?_
      refine ⟨kw.trans (VerifyKeep.of_keep tk), ?_⟩
      simp only [equationWithR, dec, Bool.toNat_false]
      exact tv
  | some r =>
    have result : v.gpr .r9 = 1 ∧ point (env v.mem b) 0 1 2 3 = r := by
      change DecodeResult b (some r) v
      with_reducible exact Eq.mp (congrArg (fun q => DecodeResult b q v)
        ((congrArg (fun m => Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) um).trans dec)) hv.2.2
    rcases result with ⟨vr, vp⟩
    refine decodedThen_ok true vr ?_ ?_
    · intro _ w wr wm
      have kw := kv.trans (VerifyKeep.of_rest wr (by decide) wm)
      refine WP.seq (WP.mono (pointTableWrite_ok (kw.ctx hc.ctx) (wm ▸ vl) 7872 (by decide) (by decide))
        fun x ⟨xk, xl, _, xp⟩ => ?_)
      have kx := kw.trans (VerifyKeep.of_powers xk (by decide) (by decide))
      have xr : tablePoint x.mem b 7872 = r :=
        xp.trans ((congrArg (fun m => point (env m b) 0 1 2 3) wm).trans vp)
      have xa : tablePoint x.mem b 7744 = tablePoint s.mem b 7744 :=
        (xk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
          ((congrArg (fun m => tablePoint m b 7744) wm).trans va)
      refine WP.mono (verifyEquationPoints_ok (hc.keep kx) xl) fun t ⟨tk, _, tv⟩ => ?_
      refine ⟨kx.trans tk, ?_⟩
      rw [xa, xr, equationResult_keep hc kx] at tv
      simp only [equationWithR, dec]
      exact tv
    · intro h; exact Bool.noConfusion h

end VG.Proof.Ed25519.Arm

import VerifiedGarbage.Proof.Ed25519.Arm.VerifyHeaders
import VerifiedGarbage.Proof.Ed25519.Arm.DecodedThen
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom

/-! Merged from `Proof.Ed25519.Arm.VerifyBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyPoints`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyRhs`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCombine`. -/
section
/-! Combine R + [k]A and load [S]B for the final point comparison. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyCombine_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa verifyCombine s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b 8000 ∧
      point (env t.mem b) 4 5 6 7 = Spec.Ed25519.pointAdd (tablePoint s.mem b 7872)
        (point (env s.mem b) 0 1 2 3) := by
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc hl) fun a ⟨ak, al, ae⟩ => ?_)
  have aq := (congrArg (fun e => point e 4 5 6 7) ae).trans (copyPointToQ_eval _)
  have ad : env a.mem b 16 = Spec.Ed25519.d := by rw [ae, copyPointToQ_d, hd]
  refine WP.seq (WP.mono (pointTableRead_ok (ak.ctx hc) al 7872 (by decide) (by decide))
    fun c ⟨ck, cl, cp, ch⟩ => ?_)
  have kc := (AccKeep.of_keep ak).trans ck
  have cq : point (env c.mem b) 4 5 6 7 = point (env s.mem b) 0 1 2 3 :=
    (point_congr _ _ _ _ (ch 4 (by decide)) (ch 5 (by decide)) (ch 6 (by decide)) (ch 7 (by decide))).trans aq
  have cp' := cp.trans (workspace_tablePoint ak.frame (by decide) (by decide))
  refine WP.seq (WP.mono (pointAdd_ok (kc.ctx hc) cl ((ch 16 (by decide)).trans ad))
    fun d ⟨dk, dl, dp, _⟩ => ?_)
  have kd := kc.trans (AccKeep.of_keep dk)
  have dp' := dp.trans (congrArg₂ Spec.Ed25519.pointAdd cp' cq)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps (kd.ctx hc) dl) fun e ⟨ek, el, ee⟩ => ?_)
  have ke := kd.trans (AccKeep.of_keep ek)
  have eqp := ((congrArg (fun f => point f 4 5 6 7) ee).trans (copyPointToQ_eval _)).trans dp'
  refine WP.mono (pointTableRead_ok (ke.ctx hc) el 8000 (by decide) (by decide))
    fun t ⟨tk, tl, tp, th⟩ => ?_
  exact ⟨ke.trans tk, tl, tp.trans (workspace_tablePoint ke.frame (by decide) (by decide)),
    (point_congr _ _ _ _ (th 4 (by decide)) (th 5 (by decide)) (th 6 (by decide)) (th 7 (by decide))).trans eqp⟩

end VG.Proof.Ed25519.Arm
end

/-! The right side reads all 512 challenge bits before the strict equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyRhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyRhs s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (Spec.Ed25519.pointEqual (tablePoint s.mem b 8000)
        (Spec.Ed25519.pointAdd (tablePoint s.mem b 7872)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64))
            (tablePoint s.mem b 7744)))).toNat := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (loadHeader_ok (ak.ctx hc.ctx) 8136 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  have kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  have cpk : PointKeep b s c := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  have cc := hc.keep (VerifyKeep.of_acc kc)
  have cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  have capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7744 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  refine WP.seq (WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 32 (by decide) (by decide)
    cc.challengeInput.fit cc.challengeInput.readable cc.challengeInput.separate) fun d ⟨dk, dl, dd, dp⟩ => ?_)
  have kd := cpk.trans dk
  have dp' : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7744) := by
    rw [hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at dp
    exact dp
  refine WP.seq (WP.mono (verifyCombine_ok (kd.ctx hc.ctx) dl dd) fun e ⟨ek, el, ep, eqp⟩ => ?_)
  have ep' := ep.trans (kd.table (by decide) (by decide))
  have eqp' := eqp.trans (congrArg₂ Spec.Ed25519.pointAdd (kd.table (by decide) (by decide)) dp')
  refine WP.mono (pointEqual_ok (ek.ctx (kd.ctx hc.ctx)) el) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨((VerifyKeep.of_point kd).trans (VerifyKeep.of_acc ek)).trans (VerifyKeep.of_keep tk), tl, ?_⟩
  exact tv.trans (congrArg (fun v : Bool => BitVec.ofNat 32 v.toNat)
    (congrArg₂ Spec.Ed25519.pointEqual ep' eqp'))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyLhs`. -/
section
/-! The left side of the equation is [S]B, retaining A and R. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyLhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyLhs s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      tablePoint t.mem b 8000 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint ∧
      tablePoint t.mem b 7744 = tablePoint s.mem b 7744 ∧
      tablePoint t.mem b 7872 = tablePoint s.mem b 7872 := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  refine WP.mono (addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  have kc : PointKeep b s c := ⟨(ar.mono (by decide)).trans (cr.mono (by decide)), by
    rw [cm, am]; exact Frame.refl _ _⟩
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (kc.ctx hc.ctx)
    (by rw [cm, am]; exact hl)) fun d ⟨dk, dl, de⟩ => ?_)
  have kd := kc.trans (PointKeep.of_keep dk)
  have dc := hc.keep (VerifyKeep.of_point kd)
  have di := dc.sigInput.suffix32
  have dp : d.gpr .r12 = sig + 32 := by rw [dk.rest.gpr _ (by decide), cp, ap, hc.sigHeader]
  have dpoint : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.basePoint :=
    (congrArg (fun e => point e 0 1 2 3) de).trans (constPoint_eval _ _)
  refine WP.seq (WP.mono (pointFromScalar_ok dc.ctx dl dp 16 (by decide) (by decide)
    di.fit di.readable di.separate) fun e ⟨ek, el, _, ep⟩ => ?_)
  have ke := kd.trans ek
  have ep' : point (env e.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint := by
    rw [(hc.sigInput.suffix32).bytes (VerifyKeep.of_point kd), dpoint] at ep
    exact ep
  refine WP.mono (pointTableWrite_ok (ke.ctx hc.ctx) el 8000 (by decide) (by decide))
    fun t ⟨tk, tl, _, tp⟩ => ?_
  refine ⟨(VerifyKeep.of_point ke).trans (VerifyKeep.of_powers tk (by decide) (by decide)), tl,
    tp.trans ep', ?_, ?_⟩
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! Compose both sides of the exact, uncofactored verification equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def equationResult (m : Mem) (sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) : Bool :=
  Spec.Ed25519.pointEqual
    (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint)
    (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a))

theorem verifyEquationPoints_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyEquationPoints s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (equationResult s.mem sig challenge
        (tablePoint s.mem b 7744) (tablePoint s.mem b 7872)).toNat := by
  refine WP.seq (WP.mono (verifyLhs_ok hc hl) fun u ⟨uk, ul, up, ua, ur⟩ => ?_)
  refine WP.mono (verifyRhs_ok (hc.keep uk) ul) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨uk.trans tk, tl, ?_⟩
  rw [up, ua, ur, hc.challengeInput.bytes uk] at tv
  exact tv

end VG.Proof.Ed25519.Arm
end

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
end

/-! Merged from `Proof.Ed25519.Arm.VerifyDecodeA`. -/
section
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
end

/-! Merged from `Proof.Ed25519.Arm.VerifyScalar`. -/
section
/-! The signature's scalar is checked canonically, before point decoding. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) :
    WP isa (.block verifyScalar) s fun t => VerifyKeep b s t ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) < Spec.Ed25519.L) := by
  unfold verifyScalar
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  have ak : VerifyKeep b s a := VerifyKeep.of_rest ar (by decide) am
  refine WP.mono (addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  have ck : VerifyKeep b s c := ak.trans (VerifyKeep.of_rest cr (by decide) cm)
  have ci := (hc.keep ck).sigInput.suffix32
  have cptr : c.gpr .r12 = sig + 32 := by rw [cp, ap, hc.sigHeader]
  refine WP.mono (unpackField_ok (ck.ctx hc.ctx) (o := SR) (src := 0) (by decide) (by decide)
    cptr (by simpa using ci.fit) (by simpa using ci.readable)
    (by simpa using ci.separate.sub_right (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun d ⟨dr, df, dl, dv⟩ => ?_
  have dk : VerifyKeep b s d := ck.trans (VerifyKeep.of_small dr (by decide) df (by decide) (by decide))
  have val : V d.mem (State.addr b) SR =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32) := by
    have dv' : V d.mem (State.addr b) SR = packedV c.mem (State.addr (sig + 32)) := by simpa only [BitVec.add_zero] using dv
    rw [dv', ← scalar_packed_decode, (hc.sigInput.suffix32).bytes ck]
  refine WP.mono (scalarCompare_ok (dk.ctx hc.ctx) dl) fun e ⟨er, ef, ev⟩ => ?_
  have ek := dk.trans (VerifyKeep.of_small er (by decide) ef (by decide) (by decide))
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨
    ek.trans (VerifyKeep.of_rest (ht.rest []) (by decide) ht.mem), ?_⟩
  rw [hz]
  change decide (e.gpr .r5 - (0 : BitVec 32) = 0) = _
  have es : e.gpr .r5 - (0 : BitVec 32) = e.gpr .r5 := BitVec.sub_zero _
  rw [es]
  have e0 : (e.gpr .r5 = 0) ↔ (e.gpr .r5).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, e0, ev, val]
  split <;> simp_all

end VG.Proof.Ed25519.Arm
end

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
end

/-! Merged from `Proof.Ed25519.Arm.VerifyContract`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyStoreHeaders`. -/
section
/-! Preserve the three input pointers beyond the verification workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyHeaders_ok {s : State} {b : BitVec 32} (hb : s.gpr .r3 = b)
    (hfit : b.toNat + 8192 ≤ 2 ^ 32) (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t => Ctx b t ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 8128, 12⟩] s.mem t.mem ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8128) 32 = s.gpr .r0 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8132) 32 = s.gpr .r1 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8136) 32 = s.gpr .r2 := by
  refine wp_movw fun a ha => wp_dp (op2_reg _ _) fun c hc => ?_
  have cp : c.gpr .r12 = b + BitVec.ofNat 32 8128 := by
    rw [hc.gpr]
    change a.gpr .r3 + a.gpr .r12 = _
    rw [ha.other _ (by decide), hb, ha.gpr]
    rfl
  have cr : Rest [.r12] s c := (ha.rest (by decide)).trans (hc.rest (by decide))
  have cm : c.mem = s.mem := hc.mem.trans ha.mem
  have ca (k : Nat) (hk : k + 8128 < 8192) :
      State.addr (c.gpr .r12 + BitVec.ofNat 32 k) = State.addr b + BitVec.ofNat 64 (8128 + k) := by
    rw [cp, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact addr_add (by omega)
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8128) (by decide)
    (by simpa only [Nat.add_zero] using ca 0 (by decide))
    (by rw [cr.wr]; exact in_base hw (by decide) (by decide)) fun d hd => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8132) (by decide)
    (by rw [hd.gpr]; exact ca 4 (by decide))
    (by rw [hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun e he => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8136) (by decide)
    (by rw [he.gpr, hd.gpr]; exact ca 8 (by decide))
    (by rw [he.wr, hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun f hf => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t := (cr.mono (by decide)).trans
    ((hd.rest _).trans ((he.rest _).trans ((hf.rest _).trans (ht.rest (by decide)))))
  have mt : t.mem = ((s.mem.writeW (State.addr b + BitVec.ofNat 64 8128) (s.gpr .r0)).writeW
      (State.addr b + BitVec.ofNat 64 8132) (s.gpr .r1)).writeW
      (State.addr b + BitVec.ofNat 64 8136) (s.gpr .r2) := by
    rw [ht.mem, hf.mem, he.mem, hd.mem, cm, he.gpr, hd.gpr,
      cr.gpr .r2 (by decide), cr.gpr .r1 (by decide), cr.gpr .r0 (by decide)]
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, kt, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hf.gpr, he.gpr, hd.gpr, cr.gpr .r3 (by decide), hb]
  · rw [mt]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  · rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [mt, Mem.readW_writeW_self32]

end VG.Proof.Ed25519.Arm
end

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
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyFinish`. -/
section
/-! Return the result and restore every callee-saved register. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyFinish_ok {s : State} {b : BitVec 32} {g : Reg → BitVec 32}
    (hc : Ctx b s) (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block verifyFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      t.mem = s.mem ∧ t.gpr .r0 = s.gpr .r9 := by
  unfold verifyFinish
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_mov (op2_reg _ _) fun u hu => WP.block_nil ?_
  refine WP.mono (scalarRestore_ok (hc.of_rest (hu.rest (ws := [Reg.r1]) (by decide)) (by decide)) (hu.mem ▸ hs))
    fun v ⟨vg, vr, vm⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨fun i hi => ?_, (hu.rest (by decide)).trans ((vr.mono (by decide)).trans (ht.rest (by decide))),
    ht.mem.trans (vm.trans hu.mem), ?_⟩
  · rw [ht.other _ (by
      have h : ∀ i < 8, scalarSavedReg i ≠ Reg.r0 := by decide
      exact h i hi)]
    exact vg i hi
  · rw [ht.gpr, vr.gpr _ (by decide), hu.gpr]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifySetup`. -/
section
/-! Save registers, install public headers, and establish the verifier context. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifySetup_ok {s : State} (h : VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VerifyContext (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) t ∧
      ScalarSaved (State.addr (s.gpr .r3)) s.gpr t.mem ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r3), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; exact List.mem_singleton_self _
  unfold verifySetup
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl h.f3 hw) fun u ⟨us, uf, ug, uk⟩ => ?_
  refine WP.mono (verifyHeaders_ok (by rw [ug]) h.f3 (by rw [uk.wr]; exact hw))
    fun t ⟨tc, tk, tf, tp, ts, th⟩ => ?_
  have kt := (uk.mono (by decide)).trans tk
  have ft : Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem :=
    (uf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
    (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  have ip (r : Reg) (n : Nat) (hn : (s.gpr r).toNat + n ≤ 2 ^ 32)
      (hi : (⟨State.addr (s.gpr r), n⟩ : Region) ∈ s.rd)
      (hd : (⟨State.addr (s.gpr r), n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
      VerifyInput (s.gpr .r3) (s.gpr r) n t := by
    refine ⟨hn, fun i hb => ?_, hd⟩
    rw [kt.rd, kt.wr]
    exact in_base (List.mem_append_left _ hi) (by omega) (by omega)
  refine ⟨⟨tc, ip .r0 32 h.f0 (by rw [h.rd]; simp) h.pk_ws,
    ip .r1 64 h.f1 (by rw [h.rd]; simp) h.sig_ws,
    ip .r2 64 h.f2 (by rw [h.rd]; simp) h.challenge_ws,
    tp.trans (congrFun ug .r0), ts.trans (congrFun ug .r1), th.trans (congrFun ug .r2)⟩,
    ?_, kt, ft⟩
  exact us.frame tf fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm
end

/-! The complete ARM verification equation restores the ABI and returns the specified flag. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyEquation_correct {s : State} (h : VerifyPre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  refine WP.seq (WP.mono (verifySetup_ok h) fun u ⟨uc, us, uk, uf⟩ => ?_)
  refine WP.seq (WP.mono (verifyBody_ok uc) fun v ⟨vk, vv⟩ => ?_)
  have vs : ScalarSaved (State.addr (s.gpr .r3)) s.gpr v.mem := us.frame vk.frame fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (verifyFinish_ok (vk.ctx uc.ctx) vs) fun t ⟨tg, tk, _, tv⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [tk.sp, vk.rest.sp, uk.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tg 0 (by decide)
    · exact tg 1 (by decide)
    · exact tg 2 (by decide)
    · exact tg 3 (by decide)
    · exact tg 4 (by decide)
    · exact tg 5 (by decide)
    · exact tg 6 (by decide)
    · exact tg 7 (by decide)
    · rw [tk.gpr _ (by decide), vk.rest.gpr _ (by decide), uk.gpr _ (by decide)]
  · have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
        Spec.Ed25519.bytesAt u.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => uf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr]
      exact hd
    rw [bytes _ _ (by decide) h.pk_ws, bytes _ _ (by decide) h.sig_ws,
      bytes _ _ (by decide) h.challenge_ws] at vv
    change (t.gpr .r0).toNat = _
    rw [tv, vv]
    cases Spec.Ed25519.verifyEquation
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 64) <;> rfl

end VG.Proof.Ed25519.Arm
end

/-! Verifier inputs are public and unchanged throughout the computation. -/
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

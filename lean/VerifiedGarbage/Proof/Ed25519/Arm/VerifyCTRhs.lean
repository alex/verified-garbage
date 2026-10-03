import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit

/-! Merged from `Proof.Ed25519.Arm.PointEqualCT`. -/
section
/-! Point comparison branches depend only on the public projective points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def EqualCTPre (base : BitVec 32) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirstCT_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) s fun t =>
      Keep base s t ∧ AllLim t.mem base ∧
      t.z = decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  refine WP.seq (WP.mono (fieldCode_ok pointEqualOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.mono (fieldEqual_ok (ka.ctx hc) la 8 9) fun t ⟨kt, lt, te, tz⟩ => ?_
  refine ⟨ka.trans kt, lt, ?_, ?_, ?_⟩
  · rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem equalSecond_ct (base : BitVec 32) (u v : Spec.X25519.Fe) :
    CT (fun s t => (Ctx base s ∧ AllLim s.mem base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Ctx base t ∧ AllLim t.mem base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (fieldEqual 10 11) (.ite .eq (.block [.mov .r9 (.imm 1)]) recoverInvalid)) (fun _ _ => True) := by
  have ht : CT (fun s t => (Ctx base s ∧ AllLim s.mem base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Ctx base t ∧ AllLim t.mem base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (fieldEqual 10 11) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : Ctx base s ∧ AllLim s.mem base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (fieldEqual 10 11) s fun t => t.z = decide (u = v) := by
    refine WP.mono (fieldEqual_ok h.1 h.2.1 10 11) fun t ⟨_, _, _, hz⟩ => ?_
    rw [hz, h.2.2.1, h.2.2.2]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    exact congrArg some (h.2.1.trans h.2.2.symm)
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : BitVec 32) (p q : Spec.Ed25519.Point) :
    CT (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      Impl.Ed25519.Arm.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : EqualCTPre base p q s) :
      WP isa (.seq (fieldCode pointEqualOps) (fieldEqual 8 9)) s fun t =>
        Ctx base t ∧ AllLim t.mem base ∧ t.z = decide (p.X * q.Z = q.X * p.Z) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (equalFirstCT_ok h.1 h.2.1) fun t ⟨kt, lt, tz, tu, tv⟩ => ?_
    refine ⟨kt.ctx h.1, lt, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.2.1, ← h.2.2.2]; rfl
    · rw [tu, ← h.2.2.1, ← h.2.2.2]; rfl
    · rw [tv, ← h.2.2.1, ← h.2.2.2]; rfl
  rw [Impl.Ed25519.Arm.pointEqual]
  apply ctSeqAssoc
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    exact congrArg some (h.2.1.2.2.1.trans h.2.2.2.2.1.symm)
  · exact (equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1, h.1.2.1.2.2.2⟩,
        ⟨h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTMul`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTLhs`. -/
section
/-! Both scalar pointer reload and [S]B have a public trace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fromCTPre_keep {b ptr : BitVec 32} {count : Nat} {s t : State}
    (h : FromCTPre b ptr count s) (hk : Keep b s t) (hl : AllLim t.mem b) : FromCTPre b ptr count t :=
  ⟨hk.ctx h.1, hl, (hk.rest.gpr _ (by decide)).trans h.2.2.1, h.2.2.2.1,
    fun i hi => by rw [hk.rest.rd, hk.rest.wr]; exact h.2.2.2.2.1 i hi, h.2.2.2.2.2⟩

theorem verifyLoadScalar_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b))
      (.block (loadHeader 8132 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => FromCTPre b (sig + 32) 16 s ∧ FromCTPre b (sig + 32) 16 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · intro s ⟨hc, hl⟩
    rw [WP.block_append_iff]
    refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun u ⟨ur, um, up⟩ => ?_
    refine WP.mono (addInput32_ok u) fun t ⟨tr, tm, tp⟩ => ?_
    have kt : VerifyKeep b s t := (VerifyKeep.of_rest ur (by decide) um).trans
      (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).sigInput.suffix32
    exact ⟨kt.ctx hc.ctx, by rw [tm, um]; exact hl, by rw [tp, up, hc.sigHeader],
      hi.fit, hi.readable, hi.separate⟩

theorem verifyConstBase_ct (b ptr : BitVec 32) :
    CT (fun s t => FromCTPre b ptr 16 s ∧ FromCTPre b ptr 16 t)
      (constPoint Spec.Ed25519.basePoint) (fun s t => FromCTPre b ptr 16 s ∧ FromCTPre b ptr 16 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.r0.trans h.2.1.r0.symm
  · intro s hs
    refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) hs.1 hs.2.1) fun t ⟨tk, tl, _⟩ => ?_
    exact fromCTPre_keep hs tk tl

theorem verifyLhs_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b)) verifyLhs (fun _ _ => True) := by
  have hm := (pointFromScalar_ct b (sig + 32) 16 (.inl rfl)).wp
    (fun s t h => ⟨WP.mono (pointFromScalar_ok h.1.1 h.1.2.1 h.1.2.2.1 16 (by decide) (by decide)
        h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2) (fun _ v => (v.1.ctx h.1.1).r0),
      WP.mono (pointFromScalar_ok h.2.1 h.2.2.1 h.2.2.2.1 16 (by decide) (by decide)
        h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2) (fun _ v => (v.1.ctx h.2.1).r0)⟩)
  refine RelCT.seq (verifyLoadScalar_ct b pk sig challenge)
    (RelCT.seq (verifyConstBase_ct b (sig + 32)) (RelCT.seq hm ?_))
  apply ctRegs [.r0] _ (by taint_decide)
  intro s t h r hr
  rw [List.mem_singleton] at hr
  subst r
  exact h.2.1.trans h.2.2.symm

end VG.Proof.Ed25519.Arm
end

/-! Verification multiplies A by every public challenge bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def verifyRhsMul : Prog isa :=
  .seq (.block (pointTableRead 7744 ++ loadHeader 8136)) (pointFromScalar 32)

theorem verifyLoadChallenge_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b))
      (.block (pointTableRead 7744 ++ loadHeader 8136))
      (fun s t => FromCTPre b challenge 32 s ∧ FromCTPre b challenge 32 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · intro s ⟨hc, hl⟩
    rw [WP.block_append_iff]
    refine WP.mono (pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun u ⟨uk, ul, _, _⟩ => ?_
    refine WP.mono (loadHeader_ok (uk.ctx hc.ctx) 8136 (by decide)) fun t ⟨tr, tm, tp⟩ => ?_
    have ku := VerifyKeep.of_acc uk
    have kt := ku.trans (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).challengeInput
    exact ⟨kt.ctx hc.ctx, tm ▸ ul, tp.trans (hc.keep ku).challengeHeader, hi.fit, hi.readable, hi.separate⟩

theorem verifyRhsMul_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b)) verifyRhsMul (fun _ _ => True) :=
  RelCT.seq (verifyLoadChallenge_ct b pk sig challenge) (pointFromScalar_ct b challenge 32 (.inr rfl))

theorem verifyRhsMul_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyRhsMul s fun t => PointKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7744) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (loadHeader_ok (ak.ctx hc.ctx) 8136 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  have kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  have cpk := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  have cc := hc.keep (VerifyKeep.of_acc kc)
  have cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  have capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7744 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  refine WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 32 (by decide) (by decide)
    cc.challengeInput.fit cc.challengeInput.readable cc.challengeInput.separate) fun t ⟨tk, tl, td, tp⟩ => ?_
  refine ⟨cpk.trans tk, tl, td, ?_⟩
  rw [hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at tp
  exact tp

end VG.Proof.Ed25519.Arm
end

/-! Verification branches only on points determined by the public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def RhsCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a r lhs : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a ∧
    tablePoint s.mem b 7872 = r ∧ tablePoint s.mem b 8000 = lhs

def CombineCTPre (b : BitVec 32) (ka r lhs : Spec.Ed25519.Point) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ env s.mem b 16 = Spec.Ed25519.d ∧
    point (env s.mem b) 0 1 2 3 = ka ∧ tablePoint s.mem b 7872 = r ∧ tablePoint s.mem b 8000 = lhs

theorem verifyMul_public_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r lhs : Spec.Ed25519.Point) :
    CT (fun s t => RhsCTPre m b pk sig challenge a r lhs s ∧ RhsCTPre m b pk sig challenge a r lhs t)
      verifyRhsMul (fun s t =>
        CombineCTPre b (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a) r lhs s ∧
        CombineCTPre b (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a) r lhs t) := by
  apply ctBoth
  · exact (verifyRhsMul_ct b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1⟩, ⟨h.2.1.ctx, h.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr, hh⟩
    refine WP.mono (verifyRhsMul_ok hp.ctx hl) fun t ⟨tk, tl, td, tp⟩ => ?_
    refine ⟨tk.ctx hp.ctx.ctx, tl, td, ?_, (tk.table (by decide) (by decide)).trans hr,
      (tk.table (by decide) (by decide)).trans hh⟩
    exact tp.trans (congrArg₂ Spec.Ed25519.pointMul (congrArg Spec.Ed25519.decodeLE hp.challengeBytes) ha)

theorem verifyCombine_ct (b : BitVec 32) (ka r lhs : Spec.Ed25519.Point) :
    CT (fun s t => CombineCTPre b ka r lhs s ∧ CombineCTPre b ka r lhs t)
      verifyCombine (fun s t => EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) s ∧
        EqualCTPre b lhs (Spec.Ed25519.pointAdd r ka) t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h reg hr
    rw [List.mem_singleton] at hr
    subst reg
    exact h.1.1.r0.trans h.2.1.r0.symm
  · intro s ⟨hc, hl, hd, hp, hr, hh⟩
    refine WP.mono (verifyCombine_ok hc hl hd) fun t ⟨tk, tl, tp, tq⟩ => ?_
    exact ⟨tk.ctx hc, tl, tp.trans hh, tq.trans (congrArg₂ Spec.Ed25519.pointAdd hr hp)⟩

theorem verifyRhs_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r lhs : Spec.Ed25519.Point) :
    CT (fun s t => RhsCTPre m b pk sig challenge a r lhs s ∧ RhsCTPre m b pk sig challenge a r lhs t)
      verifyRhs (fun _ _ => True) := by
  apply ctSeqAssoc
  exact RelCT.seq (verifyMul_public_ct m b pk sig challenge a r lhs)
    (RelCT.seq (verifyCombine_ct b _ r lhs) (pointEqual_ct b lhs _))

end VG.Proof.Ed25519.Arm

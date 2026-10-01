import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual

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

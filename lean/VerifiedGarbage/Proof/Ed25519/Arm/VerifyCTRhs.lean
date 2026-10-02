import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTMul
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqualCT

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

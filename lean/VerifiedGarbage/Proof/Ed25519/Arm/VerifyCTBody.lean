import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTDecodeA
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTScalar
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit

/-! Untrusted: the complete strict verifier leaks only its declared public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem verifyInit_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block initFields) (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
        (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.ctx.ctx.r0.trans h.2.ctx.ctx.r0.symm
  · intro s hs
    refine WP.mono (initFields_ok hs.ctx.ctx) fun t ⟨tk, tl, _⟩ => ?_
    exact ⟨hs.keep (VerifyKeep.of_keep tk), tl⟩

theorem verifyBody_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      verifyBody (fun _ _ => True) := by
  refine RelCT.seq (verifyScalar_public_ct m b pk sig challenge) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (RelCT.seq (verifyInit_ct m b pk sig challenge) (verifyDecodeA_ct m b pk sig challenge)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm

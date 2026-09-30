import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit

/-! Untrusted: canonical scalar checking loads through the public signature pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block verifyScalar) (fun _ _ => True) := by
  have head : CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block (loadHeader 8132 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro s t h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · intro s hc
      rw [WP.block_append_iff]
      refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun u ⟨ur, um, up⟩ => ?_
      refine WP.mono (addInput32_ok u) fun t ⟨tr, _, tp⟩ => ?_
      exact ⟨(tr.gpr _ (by decide)).trans ((ur.gpr _ (by decide)).trans hc.ctx.r0), by rw [tp, up, hc.sigHeader]⟩
  have tail : CT (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32))
      (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr))) (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  simpa only [verifyScalar, List.append_assoc] using ctBlockAppend head tail

theorem verifyScalar_public_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block verifyScalar) (fun s t =>
        (VerifyPublic m b pk sig challenge s ∧ s.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L)) ∧
        (VerifyPublic m b pk sig challenge t ∧ t.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L))) := by
  apply ctBoth
  · exact (verifyScalar_ct b pk sig challenge).mono (fun _ _ h => ⟨h.1.ctx, h.2.ctx⟩) (fun _ _ h => h)
  · intro s hs
    refine WP.mono (verifyScalar_ok hs.ctx) fun t ⟨tk, tz⟩ => ?_
    exact ⟨hs.keep tk, tz.trans (congrArg (fun bs => decide (Spec.Ed25519.decodeLE bs < Spec.Ed25519.L)) hs.sBytes)⟩

end VG.Proof.Ed25519.Arm

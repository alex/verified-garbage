import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit

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

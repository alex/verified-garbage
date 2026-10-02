import VerifiedGarbage.Impl.Ed25519.Arm.Recover
import VerifiedGarbage.Proof.Ed25519.Arm.Power
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Recover

/-! Candidate root and its square check agree with the decoding specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rootEnv_low (e : Env) (i : Slot) (hi : i.val < 14) : rootEnv e i = e i := by
  have h14 : i ≠ 14 := by intro h; have := congrArg Fin.val h; omega
  have h15 : i ≠ 15 := by intro h; have := congrArg Fin.val h; omega
  have h16 : i ≠ 16 := by intro h; have := congrArg Fin.val h; omega
  have h17 : i ≠ 17 := by intro h; have := congrArg Fin.val h; omega
  simp only [rootEnv, power250Env, opMul, opSqn, Function.update_of_ne h14,
    Function.update_of_ne h15, Function.update_of_ne h16, Function.update_of_ne h17]

theorem recoverCandidate_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa recoverCandidate s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_spec base a (ka.ctx hc) la) fun b ⟨kb, lb, vb⟩ => ?_)
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    rw [vb, rootEnv_low _ i hi]
  refine WP.mono (fieldCode_ok recoverFinishOps (kb.ctx (ka.ctx hc)) lb) fun t ⟨kt, lt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootEnv_eval, rootPower_eq, va, au, av3, az]
    rfl
  refine ⟨(IKeep.of_keep ka).trans (kb.trans (IKeep.of_keep kt)), lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.Arm

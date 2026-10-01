import VerifiedGarbage.Impl.Ed25519.X86.Recover
import VerifiedGarbage.Proof.Ed25519.X86.Power
import VerifiedGarbage.Proof.Ed25519.Recover

/-! Untrusted: candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

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
  have h14 : i ≠ 14 := by intro h; subst i; contradiction
  have h15 : i ≠ 15 := by intro h; subst i; contradiction
  have h16 : i ≠ 16 := by intro h; subst i; contradiction
  have h17 : i ≠ 17 := by intro h; subst i; contradiction
  simp only [rootEnv, power250Env, opMul, opSqn, Function.update_apply, h14, h15, h16, h17, ite_false]

theorem recoverCandidate_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa recoverCandidate s fun t => IKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hs) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_spec base a (ka.ctx hs)) fun b ⟨kb, eb⟩ => ?_)
  have kbr := kb
  have vb : env b.mem base 15 = VG.Proof.Ed25519.rootPower (env a.mem base 2) := by rw [eb, rootEnv_eval]
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    rw [eb]
    exact rootEnv_low _ i hi
  refine WP.mono (fieldCode_ok recoverFinishOps (kbr.ctx (ka.ctx hs))) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootPower_eq, va, au, av3, az]
    rfl
  have kar : IKeep base s a := IKeep.of_field ka
  have ktr : IKeep base b t := IKeep.of_field kt
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.X86

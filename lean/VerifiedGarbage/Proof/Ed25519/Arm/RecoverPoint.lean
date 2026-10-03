import VerifiedGarbage.Impl.Ed25519.Arm.Recover
import VerifiedGarbage.Proof.Ed25519.Arm.Power
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverSign

/-! Merged from `Proof.Ed25519.Arm.RecoverCandidate`. -/
section
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
end

/-! Candidate validation implements RFC 8032 recovery exactly. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat)
    (x y : Spec.X25519.Fe) (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa recoverSign s fun t => IKeep base s t ∧ AllLim t.mem base ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hc hl b hb) fun t ⟨tk, tl, tr⟩ => ?_
  exact ⟨IKeep.of_keep tk, tl, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa recoverPoint s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hc hl) fun a ⟨ka, la, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.ctx hc) la 11 6) fun c ⟨kc, lc, ce, cz⟩ => ?_)
  have kac := ka.trans (IKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by simp only [VG.Arm.eval, cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.ctx hc) lc b (kac.sign.trans hb) _ _ cx cy) fun t ⟨kt, lt, tr⟩ => ?_
    exact ⟨kac.trans kt, lt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.ctx hc) lc 11 12) fun d ⟨kd, ld, de, dz⟩ => ?_)
    have kacd := kac.trans (IKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by simp only [VG.Arm.eval, dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kacd.ctx hc) ld)
        fun e ⟨ke, le, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (IKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.ctx hc) le b (kacde.sign.trans hb) _ _ ex ey) fun t ⟨kt, lt, tr⟩ => ?_
      exact ⟨kacde.trans kt, lt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tm, tr⟩ => ?_
      exact ⟨kacd.trans (IKeep.of_keep kt), tm ▸ ld,
        by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.Arm

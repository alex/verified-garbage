import VerifiedGarbage.Impl.Ed25519.X86_64.RootPower
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Impl.Ed25519.X86_64.Recover
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverSign

/-! Merged from `Proof.Ed25519.X86_64.RecoverCandidate`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RootWide`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RootPower`. -/
section
/-! Decoding reuses the proved field multiplication and squaring loops. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519.X86_64

def rootEnv (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env :=
  opMul 17 17 4 (opSqn 17 17 2 (opMul 17 18 17 (opSqn 18 18 50 (opMul 18 19 18 (opSqn 19 18 100
    (opMul 18 18 17 (opSqn 18 17 50 (opMul 17 18 17 (opSqn 18 18 10 (opMul 18 19 18 (opSqn 19 18 20
    (opMul 18 18 17 (opSqn 18 17 10 (opMul 17 18 17 (opSqn 18 17 5 (opMul 17 17 18
    (opMul 18 16 16 (opMul 16 16 17 (opMul 17 4 17 (opMul 17 17 17 (opMul 17 16 16
    (opMul 16 4 4 e))))))))))))))))))))))

theorem rootPower_spec {fld : Impl.Ed25519.X86_64.Arith} [EdArith fld] (base : Addr) : ISpec base (Impl.Ed25519.X86_64.rootPower fld) rootEnv := by
  have h : ISpec base _ _ :=
    (sqrI (EdArith.ok (fld := fld)) base 16 4 ⟨by decide, by decide⟩).seq <|
    ((sqrI (EdArith.ok (fld := fld)) base 17 16 ⟨by decide, by decide⟩).append
      (sqrI (EdArith.ok (fld := fld)) base 17 17 ⟨by decide, by decide⟩)).seq <|
    ((((mulI (EdArith.ok (fld := fld)) base 17 4 17 ⟨by decide, by decide⟩).append
      (mulI (EdArith.ok (fld := fld)) base 16 16 17 ⟨by decide, by decide⟩)).append
      (sqrI (EdArith.ok (fld := fld)) base 18 16 ⟨by decide, by decide⟩)).append
      (mulI (EdArith.ok (fld := fld)) base 17 17 18 ⟨by decide, by decide⟩)).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 17 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 17 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 19 18 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 18 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 17 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 19 18 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 18 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 17 17 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI (EdArith.ok (fld := fld)) base 17 17 4 ⟨by decide, by decide⟩)
  exact h

theorem rootEnv_eval (e : VG.Proof.X25519.X86_64.Env) : rootEnv e 17 = VG.Proof.Ed25519.rootPower (e 4) := by
  simp (config := {decide := true}) only [rootEnv, opMul, opSqn, Function.update_apply]
  rfl

end VG.Proof.Ed25519.X86_64
end

/-! Lift the root exponentiation into Ed25519's larger scratch region. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr IKeep)

variable {fld : Arith} [EdArith fld]

theorem rootPowerWide_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (Impl.Ed25519.X86_64.rootPower fld) s fun t => IKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hv⟩ := rootPower_spec (fld := fld) base narrow hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, ?_⟩
  · have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
    simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e
  · change VG.Proof.X25519.X86_64.E t.mem base 17 = _
    rw [hv, rootEnv_eval, rootPower_eq]
    rfl

end VG.Proof.Ed25519.X86_64
end

/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

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

theorem recoverCandidate_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (recoverCandidate fld) s fun t => RbxKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCodeWide_ok hs recoverInitOps) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPowerWide_ok (hs.of_keep ka)) fun b ⟨kb, vb⟩ => ?_)
  have kbr : RbxKeep base a b := ⟨kb.gpr, kb.rd, kb.wr, kb.mem.mono (by decide) (by decide)⟩
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    exact Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
  refine WP.mono (fieldCodeWide_ok (kbr.scratch (hs.of_keep ka)) recoverFinishOps) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, va, au, av3, az]
    rfl
  have kar : RbxKeep base s a := ⟨fun r hr _ => ka.gpr r hr, ka.rd, ka.wr, ka.mem⟩
  have ktr : RbxKeep base b t := ⟨fun r hr _ => kt.gpr r hr, kt.rd, kt.wr, kt.mem⟩
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.X86_64
end

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

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


private theorem sign_known {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa (recoverSign fld) s fun t => RbxKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨RbxKeep.of_keep kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (recoverPoint fld) s fun t => RbxKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.scratch hs) 11 6) fun c ⟨cz, kc, ce⟩ => ?_)
  have kac := ka.trans (RbxKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by change c.zf = _; rw [cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.scratch hs) b ((kac.gpr _ (by decide) (by decide)).trans hb)
      _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kac.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.scratch hs) 11 12) fun d ⟨dz, kd, de⟩ => ?_)
    have kacd := kac.trans (RbxKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by change d.zf = _; rw [dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCodeWide_ok (kacd.scratch hs) [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (RbxKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.scratch hs) b ((kacde.gpr _ (by decide) (by decide)).trans hb)
        _ _ ex ey) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacd.trans (RbxKeep.of_keep kt), by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.X86_64

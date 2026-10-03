import VerifiedGarbage.Impl.Ed25519.AArch64.Recover
import VerifiedGarbage.Proof.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverSign

/-! Merged from `Proof.Ed25519.AArch64.RecoverCandidate`. -/
section
/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

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

theorem recoverCandidate_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa recoverCandidate s fun t => CounterKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hs) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_ok (ka.scr hs)) fun b ⟨kb, vb⟩ => ?_)
  have kbr : CounterKeep base a b := ⟨kb.gpr, kb.rd, kb.wr, kb.sp, kb.mem.mono (by decide) (by decide)⟩
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    exact Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
  refine WP.mono (fieldCode_ok recoverFinishOps (kbr.scr (ka.scr hs))) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootPower_eq, va, au, av3, az]
    rfl
  have kar : CounterKeep base s a := CounterKeep.of_keep ka
  have ktr : CounterKeep base b t := CounterKeep.of_keep kt
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.AArch64
end

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

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


private theorem sign_known {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa recoverSign s fun t => CounterKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨CounterKeep.of_keep kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa recoverPoint s fun t => CounterKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.scr hs) 11 6) fun c ⟨cz, kc, ce⟩ => ?_)
  have kac := ka.trans (CounterKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by simp only [eval, read_x, cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.scr hs) b ((kac.gpr _ (by decide) (by decide)).trans hb)
      _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kac.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.scr hs) 11 12) fun d ⟨dz, kd, de⟩ => ?_)
    have kacd := kac.trans (CounterKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by simp only [eval, read_x, dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kacd.scr hs))
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (CounterKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.scr hs) b ((kacde.gpr _ (by decide) (by decide)).trans hb)
        _ _ ex ey) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacd.trans (CounterKeep.of_keep kt), by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.AArch64

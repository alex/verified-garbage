import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual

/-! Untrusted: point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def EqualCTPre (base : Addr) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Scr s base ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirst_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      Keep base s t ∧
      eval (.zero .x .x8) t = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.scr hs) 8 9) fun t ⟨tz, kt, te⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · change some (t.gpr .x8 == 0) = _
    rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    CT (fun _ _ => True) (.block [.movz .w .x8 (if b then 1 else 0) 0]) (fun _ _ => True) := by
  cases b
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)

theorem equalSecond_ct (base : Addr) (u v : Spec.X25519.Fe) :
    CT (fun s t => (Scr s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scr t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (.block (fieldEqual 10 11)) (.ite (.zero .x .x8) (.block [.movz .w .x8 1 0]) recoverInvalid))
      (fun _ _ => True) := by
  have ht : CT (fun s t => (Scr s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scr t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.block (fieldEqual 10 11)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : Scr s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (.block (fieldEqual 10 11)) s fun t => eval (.zero .x .x8) t = some (decide (u = v)) := by
    refine WP.mono (fieldEqual_ok h.1 10 11) fun t k => ?_
    change some (t.gpr .x8 == 0) = _
    rw [k.1, h.2.1, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.trans h.2.2.symm
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : Addr) (p q : Spec.Ed25519.Point) :
    CT (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      Impl.Ed25519.AArch64.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : EqualCTPre base p q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some (decide (p.X * q.Z = q.X * p.Z)) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.scr h.1, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.1, ← h.2.2]; rfl
    · rw [tu, ← h.2.1, ← h.2.2]; rfl
    · rw [tv, ← h.2.1, ← h.2.2]; rfl
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.AArch64.pointEqual]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · exact (equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit

/-! Untrusted: point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

private theorem ctEqualOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

def EqualCTPre (base : BitVec 32) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Ctx base s ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirst_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      FieldKeep base s t ∧
      t.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.ctx hs) 8 9) fun t ⟨kt, te, tz⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · rw [tz, va, (ctEqualOps_eval _).1, (ctEqualOps_eval _).2.1]
  · rw [te 10 (by decide), va, (ctEqualOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (ctEqualOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    RelCT isa (fun _ _ => True) (.block [.mov .eax (.imm (if b then 1 else 0))]) (fun _ _ => True) := by
  cases b
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)

theorem equalSecond_ct (base : BitVec 32) (u v : Spec.X25519.Fe) :
    RelCT isa (fun s t => (Ctx base s ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Ctx base t ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (.block (fieldEqual 10 11)) (.ite .e (.block [.mov .eax (.imm 1)]) recoverInvalid))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (Ctx base s ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Ctx base t ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.block (fieldEqual 10 11)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : Ctx base s ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (.block (fieldEqual 10 11)) s fun t => t.zf = some (decide (u = v)) := by
    refine WP.mono (fieldEqual_ok h.1 10 11) fun _ k => ?_
    rw [k.2.2, h.2.1, h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.trans h.2.2.symm
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : BitVec 32) (p q : Spec.Ed25519.Point) :
    RelCT isa (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      Impl.Ed25519.X86.pointEqual (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqualCTPre base p q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Ctx base t ∧ t.zf = some (decide (p.X * q.Z = q.X * p.Z)) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.ctx h.1, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.1, ← h.2.2]; rfl
    · rw [tu, ← h.2.1, ← h.2.2]; rfl
    · rw [tv, ← h.2.1, ← h.2.2]; rfl
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.X86.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · exact (equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86

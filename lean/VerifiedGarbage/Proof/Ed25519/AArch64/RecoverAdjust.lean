import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity

/-! Sign selection and the extended coordinates of a decoded point. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩

def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem recoverSuccess_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block recoverSuccess) s fun t => Keep base s t ∧ t.gpr .x8 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (env s.mem base 0) (env s.mem base 1) := by
  rw [recoverSuccess, WP.block_append_iff]
  refine WP.mono (fieldCode_ok recoverSuccessOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (returnFlag_ok a true) fun t ⟨tr, kt⟩ => ?_
  refine ⟨ka.trans (Keep.of_keeps kt (by decide)), tr, ?_⟩
  rw [kt.mem, va]
  rfl

private theorem adjustBranch_ok {s : State} {base : Addr} (hs : Scr s base) (b : Bool)
    (hz : (s.gpr .x8 == 0) = (((env s.mem base 0).val % 2 == 1) == b)) :
    WP isa (.ite (.zero .x .x8) (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) s fun t =>
      Keep base s t ∧ env t.mem base 0 = signedX (env s.mem base 0) b ∧ env t.mem base 1 = env s.mem base 1 := by
  apply WP.ite (((env s.mem base 0).val % 2 == 1) == b) (by simp only [eval, read_x, hz])
  · intro h
    exact WP.block_nil ⟨Keep.refl _ _, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hs) fun t ⟨kt, vt⟩ => ?_
    refine ⟨kt, ?_, ?_⟩
    · rw [vt]
      change 0 - env s.mem base 0 = signedX (env s.mem base 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [vt]; rfl

theorem recoverAdjustSign_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa recoverAdjustSign s fun t => Keep base s t ∧ t.gpr .x8 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (signedX (env s.mem base 0) b) (env s.mem base 1) := by
  rw [recoverAdjustSign]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.gpr _ (by decide)).trans hb)) fun c ⟨cz, kc⟩ => ?_
  have kac : Keep base s c := (Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kc (by decide))
  have cm : c.mem = s.mem := kc.mem.trans ka.mem
  have ch : (c.gpr .x8 == 0) = (((env c.mem base 0).val % 2 == 1) == b) := by rw [cz, ax, cm]
  refine WP.seq (WP.mono (adjustBranch_ok (kac.scr hs) b ch) fun d ⟨kd, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok ((kac.trans kd).scr hs)) fun t ⟨kt, tr, tv⟩ => ?_
  exact ⟨(kac.trans kd).trans kt, tr, by rw [tv, dx, dy, cm]⟩

end VG.Proof.Ed25519.AArch64

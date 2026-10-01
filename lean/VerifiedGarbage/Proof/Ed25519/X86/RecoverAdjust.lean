import VerifiedGarbage.Proof.Ed25519.X86.RecoverParity

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem recoverSuccess_ok {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block recoverSuccess) s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (env s.mem x 0) (env s.mem x 1) := by
  rw [recoverSuccess, WP.block_append_iff]
  refine WP.mono (fieldCode_ok recoverSuccessOps hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (returnFlag_ok a x true) fun t ⟨kt, mt, rt⟩ => ?_
  exact ⟨ka.trans kt, rt, by rw [mt, ea]; rfl⟩

private theorem adjustBranch_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (b : Bool)
    (hz : s.zf = some (((env s.mem x 0).val % 2 == 1) == b)) :
    WP isa (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) s fun t =>
      FieldKeep x s t ∧ env t.mem x 0 = signedX (env s.mem x 0) b ∧ env t.mem x 1 = env s.mem x 1 := by
  apply WP.ite (((env s.mem x 0).val % 2 == 1) == b) hz
  · intro h
    exact WP.block_nil ⟨FieldKeep.refl _ _, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hc) fun t ⟨kt, et⟩ => ?_
    refine ⟨kt, ?_, ?_⟩
    · rw [et]
      change 0 - env s.mem x 0 = signedX (env s.mem x 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [et]; rfl

theorem recoverAdjustSign_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverAdjustSign s fun t => FieldKeep x s t ∧ t.gpr .eax = 1 ∧
      point (env t.mem x) 0 1 2 3 = recoveredPoint (signedX (env s.mem x 0) b) (env s.mem x 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hc 0) fun a ⟨ka, ea, va⟩ => ?_
  refine WP.mono (recoverParity_ok (ka.ctx hc) b (ka.keep.esi.trans hb)) fun c ⟨kc, mc, zc⟩ => ?_
  have ec : env c.mem x = env s.mem x := by rw [mc, ea]
  have zc' : c.zf = some (((env c.mem x 0).val % 2 == 1) == b) := by
    change fe a.mem x 64 = _ at va
    rw [zc, va, ec]
  refine WP.seq (WP.mono (adjustBranch_ok ((ka.trans kc).ctx hc) b zc') fun d ⟨kd, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok (((ka.trans kc).trans kd).ctx hc)) fun t ⟨kt, rt, pt⟩ => ?_
  exact ⟨((ka.trans kc).trans kd).trans kt, rt, by rw [pt, dx, dy, ec]⟩

end VG.Proof.Ed25519.X86

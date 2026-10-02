import VerifiedGarbage.Proof.Ed25519.Arm.RecoverParity

/-! Choose the encoded sign and finish the extended coordinates. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.mov .r9 (.imm b.toNat)]) s fun t =>
      Rest [.r9] s t ∧ t.mem = s.mem ∧ t.gpr .r9 = BitVec.ofNat 32 b.toNat := by
  refine wp_mov (op2_imm (by cases b <;> decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

theorem recoverSuccess_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa recoverSuccess s fun t => Keep base s t ∧ AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (env s.mem base 0) (env s.mem base 1) := by
  refine WP.seq (WP.mono (fieldCode_ok recoverSuccessOps hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (returnFlag_ok u true) fun t ⟨tr, tm, tv⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm ▸ ul, tv, ?_⟩
  rw [tm, ue]
  rfl

theorem adjustBranch_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hz : s.z = (((env s.mem base 0).val % 2 == 1) == b)) :
    WP isa (.ite .eq (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) s fun t =>
      Keep base s t ∧ AllLim t.mem base ∧ env t.mem base 0 = signedX (env s.mem base 0) b ∧
      env t.mem base 1 = env s.mem base 1 := by
  apply WP.ite (((env s.mem base 0).val % 2 == 1) == b) (by simp only [VG.Arm.eval, hz])
  · intro h
    exact WP.block_nil ⟨Keep.refl _ _, hl, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hc hl) fun t ⟨tk, tl, te⟩ => ?_
    refine ⟨tk, tl, ?_, ?_⟩
    · rw [te]
      change 0 - env s.mem base 0 = signedX (env s.mem base 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [te]; rfl

theorem recoverAdjustSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa recoverAdjustSign s fun t => Keep base s t ∧ AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (signedX (env s.mem base 0) b) (env s.mem base 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hc hl 0) fun a ⟨ak, al, ae, af, av⟩ => ?_
  refine WP.mono (recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun c ⟨cr, cm, cz⟩ => ?_
  have ck : Keep base s c := ak.trans ⟨cr.mono (by decide), by rw [cm]; exact Frame.refl _ _⟩
  have ce : env c.mem base = env s.mem base := (congrArg (fun m => env m base) cm).trans ae
  have ch : c.z = (((env c.mem base 0).val % 2 == 1) == b) := by rw [cz, av, ce]
  refine WP.seq (WP.mono (adjustBranch_ok (ck.ctx hc) (cm ▸ al) b ch) fun d ⟨dk, dl, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok ((ck.trans dk).ctx hc) dl) fun t ⟨tk, tl, tr, tp⟩ => ?_
  exact ⟨(ck.trans dk).trans tk, tl, tr, by rw [tp, dx, dy, ce]⟩

end VG.Proof.Ed25519.Arm

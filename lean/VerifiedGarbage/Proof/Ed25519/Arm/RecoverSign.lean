import VerifiedGarbage.Proof.Ed25519.Arm.RecoverAdjust

/-! Reject negative zero and otherwise return the selected sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def DecodeResult (base : BitVec 32) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .r9 = 0
  | some p => s.gpr .r9 = 1 ∧ point (env s.mem base) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (base : BitVec 32) :
    WP isa recoverInvalid s fun t => Keep base s t ∧ t.mem = s.mem ∧ DecodeResult base none t :=
  WP.mono (returnFlag_ok s false) fun _ ⟨tr, tm, tv⟩ =>
    ⟨⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm, tv⟩

theorem signTest_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (b : Bool)
    (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block signTest) s fun t => Rest [.r3] s t ∧ t.mem = s.mem ∧ t.z = !b := by
  refine ldr0_ok hc (by decide) fun u hu => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest _), by rw [ht.mem, hu.mem], ?_⟩
  rw [hz, hu.gpr, hb]
  cases b <;> rfl

theorem recoverSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa recoverSign s fun t => Keep base s t ∧ AllLim t.mem base ∧
      DecodeResult base (signResult (env s.mem base 0) (env s.mem base 1) b) t := by
  refine WP.seq (WP.mono (fieldZero_ok hc hl 0) fun a ⟨ak, al, ae, az⟩ => ?_)
  apply WP.ite (decide (env s.mem base 0 = 0)) (by simp only [VG.Arm.eval, az])
  · intro hzero
    have hz : env s.mem base 0 = 0 := of_decide_eq_true hzero
    refine WP.seq (WP.mono (signTest_ok (ak.ctx hc) b (ak.sign.trans hb)) fun c ⟨cr, cm, cz⟩ => ?_)
    have ck : Keep base s c := ak.trans ⟨cr.mono (by decide), by rw [cm]; exact Frame.refl _ _⟩
    have cl : AllLim c.mem base := cm ▸ al
    have ce : env c.mem base = env s.mem base := (congrArg (fun m => env m base) cm).trans ae
    apply WP.ite b (by simp only [VG.Arm.eval, cz, Bool.not_not])
    · intro ht
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨tk, tm, tr⟩ => ?_
      refine ⟨ck.trans tk, tm ▸ cl, ?_⟩
      simpa only [signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (recoverAdjustSign_ok (ck.ctx hc) cl b (ck.sign.trans hb)) fun t ⟨tk, tl, tr, tv⟩ => ?_
      refine ⟨ck.trans tk, tl, ?_⟩
      simp only [signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, DecodeResult]
      exact ⟨tr, by rw [tv, ce, hf]⟩
  · intro hnonzero
    have hn : env s.mem base 0 ≠ 0 := of_decide_eq_false hnonzero
    refine WP.mono (recoverAdjustSign_ok (ak.ctx hc) al b (ak.sign.trans hb)) fun t ⟨tk, tl, tr, tv⟩ => ?_
    refine ⟨ak.trans tk, tl, ?_⟩
    simp only [signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨tr, by rw [tv, ae]⟩

end VG.Proof.Ed25519.Arm

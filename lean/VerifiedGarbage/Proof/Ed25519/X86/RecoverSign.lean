import VerifiedGarbage.Proof.Ed25519.X86.RecoverAdjust

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def DecodeResult (x : BitVec 32) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .eax = 0
  | some p => s.gpr .eax = 1 ∧ point (env s.mem x) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (x : BitVec 32) :
    WP isa recoverInvalid s fun t => FieldKeep x s t ∧ DecodeResult x none t :=
  WP.mono (returnFlag_ok s x false) fun _ ⟨kt, _, rt⟩ => ⟨kt, rt⟩

theorem signTest_ok {s : State} (x : BitVec 32) (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t => FieldKeep x s t ∧ t.mem = s.mem ∧
      isa.eval .ne t = some b := by
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨FieldKeep.of_mem ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩ ht.mem, ht.mem, ?_⟩
  show t.zf.map (!·) = _
  rw [zt, BitVec.and_self, hb]
  cases b <;> rfl

theorem recoverSign_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa recoverSign s fun t => FieldKeep x s t ∧
      DecodeResult x (signResult (env s.mem x 0) (env s.mem x 1) b) t := by
  refine WP.seq (WP.mono (fieldZero_ok hc 0) fun a ⟨ka, ea, za⟩ => ?_)
  apply WP.ite (decide (env s.mem x 0 = 0)) za
  · intro hzero
    have hz := of_decide_eq_true hzero
    refine WP.seq (WP.mono (signTest_ok x b (ka.keep.esi.trans hb)) fun c ⟨kc, mc, zc⟩ => ?_)
    have ec : env c.mem x = env s.mem x := by rw [mc, ea]
    apply WP.ite b zc
    · intro ht
      refine WP.mono (recoverInvalid_ok c x) fun t ⟨kt, tr⟩ => ?_
      refine ⟨(ka.trans kc).trans kt, ?_⟩
      simpa only [signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (recoverAdjustSign_ok ((ka.trans kc).ctx hc) b
        (kc.keep.esi.trans (ka.keep.esi.trans hb))) fun t ⟨kt, rt, pt⟩ => ?_
      refine ⟨(ka.trans kc).trans kt, ?_⟩
      simp only [signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, DecodeResult]
      exact ⟨rt, by rw [ec, hf] at pt; exact pt⟩
  · intro hnonzero
    have hn := of_decide_eq_false hnonzero
    refine WP.mono (recoverAdjustSign_ok (ka.ctx hc) b (ka.keep.esi.trans hb)) fun t ⟨kt, rt, pt⟩ => ?_
    refine ⟨ka.trans kt, ?_⟩
    simp only [signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨rt, by rw [ea] at pt; exact pt⟩

end VG.Proof.Ed25519.X86

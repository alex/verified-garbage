import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverAdjust

/-! Reject the negative encoding of zero and otherwise return the selected sign. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def DecodeResult (base : Addr) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .rax = 0
  | some p => s.gpr .rax = 1 ∧ point (env s.mem base) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (base : Addr) :
    WP isa recoverInvalid s fun t => Keep base s t ∧ DecodeResult base none t :=
  WP.mono (returnFlag_ok s false) fun _ ⟨tr, kt⟩ => ⟨Keep.of_keeps kt (by decide), tr⟩

theorem recoverSign_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (recoverSign fld) s fun t => Keep base s t ∧
      DecodeResult base (signResult (env s.mem base 0) (env s.mem base 1) b) t := by
  rw [recoverSign]
  refine WP.seq (WP.mono (fieldZero_ok hs 0) fun a ⟨az, ka, am⟩ => ?_)
  apply WP.ite (decide (env s.mem base 0 = 0)) (by exact az)
  · intro hzero
    have hz : env s.mem base 0 = 0 := of_decide_eq_true hzero
    refine WP.seq (WP.mono (testSign_ok b ((ka.gpr _ (by decide)).trans hb)) fun c ⟨cz, kc⟩ => ?_)
    have kac := ka.trans (Keep.of_keeps kc (by decide))
    apply WP.ite b (by simp only [eval, cz, Option.map_some, Bool.not_not])
    · intro ht
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
      refine ⟨kac.trans kt, ?_⟩
      simpa only [signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (recoverAdjustSign_ok (hs.of_keep kac) b ((kac.gpr _ (by decide)).trans hb))
        fun t ⟨kt, tr, tv⟩ => ?_
      refine ⟨kac.trans kt, ?_⟩
      simp only [signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, DecodeResult]
      exact ⟨tr, by rw [tv, kc.2.1, am, hf]⟩
  · intro hnonzero
    have hn : env s.mem base 0 ≠ 0 := of_decide_eq_false hnonzero
    refine WP.mono (recoverAdjustSign_ok (hs.of_keep ka) b ((ka.gpr _ (by decide)).trans hb))
      fun t ⟨kt, tr, tv⟩ => ?_
    refine ⟨ka.trans kt, ?_⟩
    simp only [signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨tr, by rw [tv, am]⟩

end VG.Proof.Ed25519.X86_64

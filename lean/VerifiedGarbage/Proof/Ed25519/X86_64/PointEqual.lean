import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverSign

/-! Projective comparison implements the specification's pointEqual. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem equalOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (Impl.Ed25519.X86_64.pointEqual fld) s fun t => Keep base s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual (point (env s.mem base) 0 1 2 3)
        (point (env s.mem base) 4 5 6 7)) := by
  rw [Impl.Ed25519.X86_64.pointEqual]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs pointEqualOps) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (hs.of_keep ka) 8 9) fun b ⟨bz, kb, be⟩ => ?_
  have kab := ka.trans kb
  have bx : b.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) := by
    rw [bz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  apply WP.ite _ bx
  · intro htx
    have hx := of_decide_eq_true htx
    refine WP.seq (WP.mono (fieldEqual_ok (hs.of_keep kab) 10 11) fun c ⟨cz, kc, _⟩ => ?_)
    have cy : c.zf = some (decide (env s.mem base 1 * env s.mem base 6 = env s.mem base 5 * env s.mem base 2)) := by
      rw [cz, be 10 (by decide), be 11 (by decide), va, (equalOps_eval _).2.2.1, (equalOps_eval _).2.2.2]
    apply WP.ite _ cy
    · intro hty
      have hy := of_decide_eq_true hty
      refine WP.mono (returnFlag_ok c true) fun t ⟨tr, kt⟩ => ?_
      refine ⟨(kab.trans kc).trans (Keep.of_keeps kt (by decide)), ?_⟩
      simpa only [Spec.Ed25519.pointEqual, point, hx, hy, beq_self_eq_true, Bool.and_self] using tr
    · intro hfy
      have hy := of_decide_eq_false hfy
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
      refine ⟨(kab.trans kc).trans kt, ?_⟩
      simpa only [Spec.Ed25519.pointEqual, point, hx, beq_self_eq_true, beq_eq_false_iff_ne.mpr hy,
        Bool.and_false, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr
  · intro hfx
    have hx := of_decide_eq_false hfx
    refine WP.mono (recoverInvalid_ok b base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨kab.trans kt, ?_⟩
    simpa only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr hx, Bool.false_and, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr

end VG.Proof.Ed25519.X86_64

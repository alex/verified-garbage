import VerifiedGarbage.Proof.Ed25519.Arm.WordsZero
import VerifiedGarbage.Proof.Ed25519.Arm.Freeze

/-! Canonical representatives give exact field comparisons. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open Fin.CommRing

theorem fieldZero_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b) (a : Slot) :
    WP isa (fieldZero a) s fun t => Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = env s.mem b ∧
      t.z = decide (env s.mem b a = 0) := by
  refine WP.seq (WP.mono (freeze_ok hc hl a) fun u ⟨uk, ul, ue, uf, uv⟩ => ?_)
  refine WP.mono (wordsZero_ok (uk.ctx hc) FR (by decide) uf) fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => env m b) tm).trans ue, ?_⟩
  rw [tz, uv]
  have he : (env s.mem b a).val = 0 ↔ env s.mem b a = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (a b : Slot) :
    WP isa (fieldEqual a b) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      (∀ i : Slot, i ≠ 21 → env t.mem base i = env s.mem base i) ∧
      t.z = decide (env s.mem base a = env s.mem base b) := by
  refine WP.seq (WP.mono (fieldCode_ok [.sub 21 a b] hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (fieldZero_ok (uk.ctx hc) ul 21) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨uk.trans tk, tl, fun i hi => ?_, ?_⟩
  · rw [te, ue]
    exact Function.update_of_ne hi _ _
  · rw [tz, ue]
    change decide (env s.mem base a - env s.mem base b = 0) = _
    simp only [sub_eq_zero]

end VG.Proof.Ed25519.Arm

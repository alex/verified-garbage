import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.WordsEqual
import VerifiedGarbage.Proof.Ed25519.Arm.Freeze

/-! Equality with the canonical representative rejects y >= p. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem canonicalY_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa canonicalY s fun t => Keep base s t ∧ AllLim t.mem base ∧ env t.mem base = env s.mem base ∧
      t.z = decide (V s.mem (State.addr base) (offset 1) < Spec.X25519.P) := by
  refine WP.seq (WP.mono (freezeRaw_ok hc hl 1) fun u ⟨uk, ul, ue, uf, uv, uraw⟩ => ?_)
  refine WP.mono (wordsEqual_ok (uk.ctx hc) (offset 1) FR (by decide) (by decide) (ul 1) uf)
    fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => env m base) tm).trans ue, ?_⟩
  have vy : V u.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) :=
    val16_congr (uraw 1)
  rw [tz, vy, uv]
  change decide (V s.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % Spec.X25519.P) = _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact h ▸ Nat.mod_lt _ (by decide)
  · intro h
    exact (Nat.mod_eq_of_lt h).symm

end VG.Proof.Ed25519.Arm

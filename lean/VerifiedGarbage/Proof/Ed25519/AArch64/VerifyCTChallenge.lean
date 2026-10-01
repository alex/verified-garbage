import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyChallenge
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVarBatchCT

/-! Untrusted: the number of batches in `[k]A` depends only on the public challenge. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- The challenge read through `x1`, the same in both runs, with its upper
words readable. -/
def ChallengeCTPre (base k : Addr) (scalar : Nat) (s : State) : Prop :=
  ScalarVarCTPre 32 base k scalar s ∧
    ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off k 32) d) 8

theorem challengeHigh_pre {s : State} {base k : Addr} {scalar : Nat} (h : ChallengeCTPre base k scalar s) :
    WP isa (.block challengeHigh) s fun t => ScalarVarCTPre 32 base k scalar t ∧
      eval (.zero .x .x8) t = some (decide (scalar < 2 ^ 256)) ∧
      (scalar < 2 ^ 256 → ScalarVarCTPre 16 base k scalar t) := by
  obtain ⟨⟨⟨hs, hp, hr, hf⟩, hv⟩, hw⟩ := h
  have hv' : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 64) = scalar := hv
  refine WP.mono (challengeHigh_ok hp hw) fun t ⟨tz, kt⟩ => ?_
  have ts := hs.of_keeps kt (by decide)
  have tp : t.gpr .x1 = k := (kt.gpr _ (by decide)).trans hp
  have tr : ∀ i < 2 * 32, InRegions (t.rd ++ t.wr) (off k i) 1 := by
    intro i hi; rw [kt.rd, kt.wr]; exact hr i hi
  refine ⟨⟨⟨ts, tp, tr, hf⟩, by rw [kt.mem]; exact hv⟩, by rw [tz, hv'], fun hlt => ?_⟩
  refine ⟨⟨ts, tp, fun i hi => tr i (by omega), fun i hi => hf i (by omega)⟩, ?_⟩
  change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem k 32) = scalar
  rw [kt.mem, ← challenge_low (by rw [hv']; exact hlt), hv']

theorem challengeMul_ct (base k : Addr) (scalar : Nat) :
    CT (fun s t => ChallengeCTPre base k scalar s ∧ ChallengeCTPre base k scalar t)
      challengeMul (fun _ _ => True) := by
  have hb : CT (fun s t => ChallengeCTPre base k scalar s ∧ ChallengeCTPre base k scalar t)
      (.block challengeHigh) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x1]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.1.1.2.1.trans h.2.1.1.2.1.symm
  rw [challengeMul]
  refine seq_runs hb (fun x h => challengeHigh_pre h) (fun y h => challengeHigh_pre h) ?_
  refine CT.ite (fun x y h => h.1.2.1.trans h.2.2.1.symm) ?_ ?_
  · refine (pointFromScalarVar16_ct base k scalar).mono (fun x y h => ?_) (fun _ _ h => h)
    have hlt : scalar < 2 ^ 256 := by
      have e := h.2.symm.trans h.1.1.2.1
      exact of_decide_eq_true (Option.some.inj e).symm
    exact ⟨h.1.1.2.2 hlt, h.1.2.2.2 hlt⟩
  · exact (pointFromScalarVar32_ct base k scalar).mono (fun x y h => ⟨h.1.1.1, h.1.2.1⟩)
      (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64

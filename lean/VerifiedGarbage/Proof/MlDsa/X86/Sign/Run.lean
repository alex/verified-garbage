import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseC

/-!
# ML-DSA signing on x86 (32-bit): what two related runs agree on

Whether every entry of `Â` was sampled (`Good`), and the number of iterations
of the loop (`NI`: the number the implementation's `SampleInBall` and the
checks make, or 1 if `Â` was not sampled), are the same in two runs related by
`SPub`; and at an iteration both reach (`t < NI`), so are `c̃`, whether
`SampleInBall` succeeded, whether the checks passed, and then the hint.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

section
variable (p : Params) (F : PrimsOk P)

/-- Every entry of `Â` was sampled. -/
abbrev Good (s₀ : State) : Prop := okE p F.rejF s₀ (p.k * p.ℓ) = true

/-- The number of iterations of the loop. -/
def NI (s₀ : State) : Nat := if Good p F s₀ then itV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF else 1

/-- The inputs, on entry. -/
abbrev sk₀ (s₀ : State) : List Byte := skOf p s₀

end

theorem NI_pos (F : PrimsOk P) (s₀ : State) : 0 < NI p F s₀ := by
  unfold NI; split
  · exact nIt_pos _ (by decide)
  · decide

theorem NI_le (F : PrimsOk P) (s₀ : State) : NI p F s₀ ≤ 814 := by
  unfold NI; split
  · exact nIt_le _ _
  · decide

theorem NI_good {F : PrimsOk P} {s₀ : State} (h : Good p F s₀) :
    NI p F s₀ = itV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF := by
  unfold NI; rw [ifp h]

theorem seedE_eq {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') (e : Nat) : seedE p s₀ e = seedE p s₀' e := by
  show aSeed (rhoS p s₀) _ _ = aSeed (rhoS p s₀') _ _; rw [rhoS_eq ps hq]

theorem okE_eq {F : List Byte → Bool} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') (e : Nat) :
    okE p F s₀ e = okE p F s₀' e := by
  simp only [okE, seedE_eq ps hq]

theorem skOf_len (ps : PS p) (s₀ : State) : 32 ≤ (skOf p s₀).length := by
  rw [VG.Proof.MlKem.bytesAt_length]; exact skLen_ge ps

/-- `ExpandA` succeeds within `maxBounds` once every entry was sampled. -/
theorem expandA_good {F : PrimsOk P} {s₀ : State} (h : Good p F s₀) :
    expandA p maxBounds (rhoV (skOf p s₀)) = some (amat p (Av (skOf p s₀))) := by
  refine expandA_some fun i hi j hj => ?_
  have hl : 0 < p.ℓ := by omega
  have he := okE_lt h (aIdx hi hj)
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2] at he
  exact F.rejMax _ he

theorem leakV_eq {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (h : Good p F s₀) (h' : Good p F s₀')
    (hq : SPub p s₀ s₀') :
    leakV p (skOf p s₀) (muOf s₀) (rndOf s₀) = leakV p (skOf p s₀') (muOf s₀') (rndOf s₀') :=
  leakV_of_leak (skOf_len ps s₀) (skOf_len ps s₀') (expandA_good h) (expandA_good h') hq.2

theorem good_iff {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : Good p F s₀ ↔ Good p F s₀' := by
  simp only [Good, okE_eq ps hq]

theorem NI_eq {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : NI p F s₀ = NI p F s₀' := by
  by_cases h : Good p F s₀
  · have h' := (good_iff ps hq).mp h
    rw [NI_good h, NI_good h']
    exact itV_eq ps.hok F.ballMax (leakV_eq ps h h' hq)
  · have h' : ¬ Good p F s₀' := fun h' => h ((good_iff ps hq).mpr h')
    unfold NI; rw [ifn h, ifn h']

/-- Iteration `t` is run. -/
def Run (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Prop := Good p F s₀ ∧ t < NI p F s₀

instance {F : PrimsOk P} {t : Nat} {s₀ : State} : Decidable (Run p F t s₀) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Run.cont {F : PrimsOk P} {t : Nat} {s₀ : State} (h : Run p F t s₀) :
    ∀ j < t, contV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF j = true := by
  have := h.2; rw [NI_good h.1] at this
  exact nIt_before _ this

theorem Run.lt {F : PrimsOk P} {t : Nat} {s₀ : State} (h : Run p F t s₀) : t < 814 :=
  Nat.lt_of_lt_of_le h.2 (NI_le F s₀)

theorem run_iff {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') :
    Run p F t s₀ ↔ Run p F t s₀' := by
  simp only [Run, good_iff ps hq, NI_eq ps hq]

/-- At an iteration both runs reach: `c̃`, the success of `SampleInBall`,
the outcome of the checks, and the hint. -/
theorem run_at {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') (h : Run p F t s₀) :
    CTv p s₀ (p.ℓ * t) = CTv p s₀' (p.ℓ * t) ∧
      (F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true →
        (passV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t) ↔ passV p (skOf p s₀') (muOf s₀') (rndOf s₀') (p.ℓ * t)) ∧
        (passV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t) →
          hbitsV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t) = hbitsV p (skOf p s₀') (muOf s₀') (rndOf s₀') (p.ℓ * t))) :=
  leak_at ps.hok F.ballMax (leakV_eq ps h.1 ((good_iff ps hq).mp h.1) hq) (by show t < 1000; have := h.lt; omega) h.cont

end VG.Proof.MlDsa.X86.Sign

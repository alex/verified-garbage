import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVar
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVarLit
import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport

/-!
# Variable-time bit loops: what their traces depend on

Untrusted. The bit loop branches on the scalar's bits, so its trace depends
on the scalar: both runs must multiply by the same scalar (in verification,
the public inputs are the same in both runs). Everything else is public by
the taint analysis or, for the branches, by correctness.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- Chains two programs whose runs each satisfy a predicate of their own. -/
theorem seq_runs {A₁ A₂ B₁ B₂ : State → Prop} {Q : State → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : CT (fun x y => A₁ x ∧ A₂ y) c₁ (fun _ _ => True))
    (w₁ : ∀ x, A₁ x → WP isa c₁ x B₁) (w₂ : ∀ y, A₂ y → WP isa c₁ y B₂)
    (h₂ : CT (fun x y => B₁ x ∧ B₂ y) c₂ Q) :
    CT (fun x y => A₁ x ∧ A₂ y) (.seq c₁ c₂) Q :=
  CT.seq ((CT.wp h₁ fun x y h => ⟨w₁ x h.1, w₂ y h.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) h₂

/-- After the bit load: what the rest of the loop body's trace depends on. -/
def VarBitLoaded (base : Addr) (n bit : Nat) (s : State) : Prop :=
  s.gpr .x0 = base ∧ s.gpr .x19 = BitVec.ofNat 64 n ∧ eval (.nonzero .x .x3) s = some (decide (bit ≠ 0))

theorem varBitBlock_ok {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {s₀ s : State} {base : Addr}
    {start scalar n : Nat} {p : Spec.Ed25519.Point} (hi : start + 16 ≤ 512)
    (h : AccumulateVarInv f s₀ base start scalar p (n + 1) s) :
    WP isa (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ scalarBitLoad)) s
      (VarBitLoaded base n ((scalar / 2 ^ (start + n)) % 2)) := by
  have hn : n < 16 := by have := h.bound; omega
  rw [WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n h.counter) fun a ⟨ac, ka⟩ => ?_
  refine WP.mono (scalarBitLoad_ok (h.scratch.of_keeps ka (by decide)) n start
    ((scalar / 2 ^ (start + n)) % 2) (by omega) (by omega) ac
    ((ka.gpr _ (by decide)).trans h.startReg) (by rw [ka.mem]; exact h.bits n hn)) fun b ⟨bz, kb⟩ => ?_
  exact ⟨(kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans h.scratch.x0),
    (kb.gpr _ (by decide)).trans ac, bz⟩

/-- What the trace of an addition of a table entry depends on. -/
def AddEntryCT (add : List Instr) : Prop :=
  CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19) (.block (addEntry add)) (fun _ _ => True)

theorem accumulateVarBody_ct {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddEntryCT add) {s₁ s₂ : State} {base : Addr} {start scalar n : Nat}
    {p₁ p₂ : Spec.Ed25519.Point} (hi : start + 16 ≤ 512) :
    CT (fun x y => AccumulateVarInv f s₁ base start scalar p₁ (n + 1) x ∧
      AccumulateVarInv f s₂ base start scalar p₂ (n + 1) y) (accumulateVarBody add) (fun _ _ => True) := by
  rw [accumulateVarBody]
  refine seq_runs ?_ (fun x h => varBitBlock_ok hi h) (fun y h => varBitBlock_ok hi h) ?_
  · apply CT.taint (Taint.ofRegs [.x0, .x19, .x1]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.scratch.x0.trans h.2.scratch.x0.symm
    · exact h.1.counter.trans h.2.counter.symm
    · exact h.1.startReg.trans h.2.startReg.symm
  · refine CT.ite ?_ ?_ ?_
    · intro x y h
      rw [h.1.2.2, h.2.2.2]
    · exact hadd.mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.1.trans h.1.2.2.1.symm⟩)
        (fun _ _ h => h)
    · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
      exact fun _ _ _ => agree_ofRegs (by simp)

theorem accumulateVarLoop_ct {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) (hct : AddEntryCT add)
    (s₁ s₂ : State) (base : Addr) (start scalar : Nat) (p₁ p₂ : Spec.Ed25519.Point)
    (hi : start + 16 ≤ 512) (n : Nat) :
    CT (fun x y => AccumulateVarInv f s₁ base start scalar p₁ n x ∧
      AccumulateVarInv f s₂ base start scalar p₂ n y) (.loop (accumulateVarBody add) (.nonzero .x .x19))
      (fun _ _ => True) := by
  apply CT.loop (fun n x y => AccumulateVarInv f s₁ base start scalar p₁ n x ∧
    AccumulateVarInv f s₂ base start scalar p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply CT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    have hw := withRuns (accumulateVarBody_ct (f := f) (s₁ := s₁) (s₂ := s₂) (p₁ := p₁) (p₂ := p₂)
      (base := base) (start := start) (n := j) (scalar := scalar) hct hi)
      (fun x y h => ⟨accumulateVarStep_ok hadd hi h.1, accumulateVarStep_ok hadd hi h.2⟩)
    refine hw.mono (fun _ _ h => h) ?_
    intro x y ⟨_, a, b, hab, hx, hy⟩
    have hj : j < 16 := by have := hab.1.bound; omega
    have ex : eval (.nonzero .x .x19) x = some (decide (j ≠ 0)) := by
      simp only [eval, read_x, hx.1, point_counter_nonzero j hj]
    have ey : eval (.nonzero .x .x19) y = some (decide (j ≠ 0)) := by
      simp only [eval, read_x, hy.1, point_counter_nonzero j hj]
    refine ⟨ex.trans ey.symm, fun _ => trivial, fun he => ?_⟩
    have hj0 : j ≠ 0 := by
      intro hz
      subst j
      simp only [ex, show decide ((0 : Nat) ≠ 0) = false from rfl] at he
      cases he
    exact ⟨j, by omega, hx.2.2.2.2 hj0, hy.2.2.2.2 hj0⟩

theorem accumulateVar16_ct {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) (hct : AddEntryCT add)
    (base : Addr) (start scalar : Nat) (p₁ p₂ : Spec.Ed25519.Point) (hi : start + 16 ≤ 512) :
    CT (fun x y => AccumulateVarPre f base start scalar p₁ x ∧
      AccumulateVarPre f base start scalar p₂ y) (accumulateVar16 add) (fun _ _ => True) := by
  rw [accumulateVar16]
  have hinit : CT (fun x y => AccumulateVarPre f base start scalar p₁ x ∧
      AccumulateVarPre f base start scalar p₂ y) (.block [.movz .w .x19 16 0]) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)
  refine CT.seq (withRuns hinit (fun x y _ => ⟨accumulateInit_ok x, accumulateInit_ok y⟩)) ?_
  intro x y tx ty x' y' ⟨hsp, _, a, b, hab, ⟨xc, xk⟩, ⟨yc, yk⟩⟩ ex ey
  exact accumulateVarLoop_ct hadd hct a b base start scalar p₁ p₂ hi 16 _ _ _ _ _ _
    ⟨hsp, hab.1.init xc xk, hab.2.init yc yk⟩ ex ey

theorem addEntryExact_ct : AddEntryCT pointAdd := by
  apply CT.taint (Taint.ofRegs [.x0, .x19]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem addEntryCached_ct : AddEntryCT pointAddCached := by
  apply CT.taint (Taint.ofRegs [.x0, .x19]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

end VG.Proof.Ed25519.AArch64

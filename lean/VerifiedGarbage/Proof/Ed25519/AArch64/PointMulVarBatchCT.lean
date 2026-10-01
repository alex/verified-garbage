import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVarBatch
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVarCT
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCT
import VerifiedGarbage.Proof.Ed25519.AArch64.PointFromScalarCT
import VerifiedGarbage.Proof.Ed25519.AArch64.BaseMultiplyCT
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit

/-!
# Variable-time scalar multiplication: what the traces depend on

Untrusted. Both runs multiply by the same scalar. Each stage of a batch is
public by the taint analysis or by `accumulateVar16_ct`, and the facts each
run needs between the stages come from the correctness proof's stages.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem pointMulBatchVar_ct {s₁ s₂ : State} {base : Addr} {count scalar j : Nat}
    {p₁ p₂ : Spec.Ed25519.Point} (hj : j < count) (hn : count ≤ 32) :
    CT (fun x y => PointMulInv s₁ base count scalar p₁ (j + 1) x ∧
      PointMulInv s₂ base count scalar p₂ (j + 1) y) pointMulBatchVar (fun _ _ => True) := by
  rw [pointMulBatchVar]
  refine seq_runs ?_ (fun x h => varBegin_ok hn h) (fun y h => varBegin_ok hn h) ?_
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  refine seq_runs ?_ (fun x h => varPrepare_ok hj hn h) (fun y h => varPrepare_ok hj hn h) ?_
  · apply CT.taint (Taint.ofRegs [.x0, .x19]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.scratch.x0.trans h.2.1.scratch.x0.symm
    · exact h.1.2.trans h.2.2.symm
  refine seq_runs ?_ (fun x h => varOffset_ok hj hn h) (fun y h => varOffset_ok hj hn h) ?_
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.1.scratch.x0 h.2.1.scratch.x0
  refine seq_runs ?_ (fun x h => varAccumulate_ok hj hn h) (fun y h => varAccumulate_ok hj hn h) ?_
  · exact (accumulateVar16_ct (f := id) pointAdd_spec addEntryExact_ct base (16 * j) scalar p₁ p₂
      (by omega)).mono (fun _ _ h => ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.scratch.x0 h.2.scratch.x0

theorem pointMulLoopVar_ct (s₁ s₂ : State) (base : Addr) (count scalar : Nat)
    (p₁ p₂ : Spec.Ed25519.Point) (hn : count ≤ 32) (n : Nat) :
    CT (fun x y => PointMulInv s₁ base count scalar p₁ n x ∧
      PointMulInv s₂ base count scalar p₂ n y) (.loop pointMulBatchVar (.nonzero .x .x19))
      (fun _ _ => True) := by
  apply CT.loop (fun n x y => PointMulInv s₁ base count scalar p₁ n x ∧
    PointMulInv s₂ base count scalar p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply CT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < count
    · have hw := withRuns (pointMulBatchVar_ct (s₁ := s₁) (s₂ := s₂) (p₁ := p₁) (p₂ := p₂)
        (base := base) (scalar := scalar) hj hn)
        (fun x y h => ⟨pointMulBatchVar_ok hj hn h.1, pointMulBatchVar_ok hj hn h.2⟩)
      refine hw.mono (fun _ _ h => h) ?_
      intro x y ⟨_, a, b, _, ⟨hx, xz⟩, ⟨hy, yz⟩⟩
      have ex : eval (.nonzero .x .x19) x = some (decide (j ≠ 0)) := by
        simp only [eval, read_x, xz, batch_counter_nonzero j (by omega)]
      have ey : eval (.nonzero .x .x19) y = some (decide (j ≠ 0)) := by
        simp only [eval, read_x, yz, batch_counter_nonzero j (by omega)]
      refine ⟨ex.trans ey.symm, fun _ => trivial, fun he => ?_⟩
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp only [ex, show decide ((0 : Nat) ≠ 0) = false from rfl] at he
        cases he
      exact ⟨j, by omega, ⟨by omega, by omega, hx.scratch, hx.counter, hx.d, hx.value, hx.bits, hx.table,
        hx.keep⟩, ⟨by omega, by omega, hy.scratch, hy.counter, hy.d, hy.value, hy.bits, hy.table, hy.keep⟩⟩
    · apply CT.of_false
      intro x y h
      have := h.1.bound
      omega

theorem pointMultiplyVar_ct_of_init (count : Nat) (base : Addr) (scalar : Nat)
    (hn0 : 0 < count) (hn : count ≤ 32)
    (initCT : CT (fun x y => MulCTPreN count base scalar x ∧ MulCTPreN count base scalar y)
      (pointMultiplyInit count) (fun _ _ => True)) :
    CT (fun x y => MulCTPreN count base scalar x ∧ MulCTPreN count base scalar y)
      (pointMultiplyVar count) (fun _ _ => True) := by
  have hi := withRuns initCT (fun x y h =>
    ⟨pointMultiplyInit_ok h.1.1 count scalar hn0 hn h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     pointMultiplyInit_ok h.2.1 count scalar hn0 hn h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [pointMultiplyVar]
  refine CT.seq hi ?_
  intro x y tx ty x' y' ⟨hsp, _, a, b, _, hx, hy⟩ ex ey
  exact pointMulLoopVar_ct a b base count scalar _ _ hn count _ _ _ _ _ _ ⟨hsp, hx, hy⟩ ex ey

/-- A scalar read through `x1`, the same in both runs. -/
def ScalarVarCTPre (count : Nat) (base k : Addr) (scalar : Nat) (s : State) : Prop :=
  ScalarCTPre count base k s ∧ Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k (2 * count)) = scalar

theorem pointFromScalarVar32_ct (base k : Addr) (scalar : Nat) :
    CT (fun s t => ScalarVarCTPre 32 base k scalar s ∧ ScalarVarCTPre 32 base k scalar t)
      (pointFromScalarVar 32) (fun _ _ => True) := by
  have hp : CT (fun s t => ScalarVarCTPre 32 base k scalar s ∧ ScalarVarCTPre 32 base k scalar t)
      (pointFromScalarPrepare 32) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1]) _ (by taint_decide)
    exact fun _ _ h => scalarInput_agree ⟨h.1.1, h.2.1⟩
  have hp' := withRuns hp (fun s t h =>
    ⟨pointFromScalarPrepare_ok h.1.1.1 h.1.1.2.1 32 (by decide) (by decide) h.1.1.2.2.1 h.1.1.2.2.2,
     pointFromScalarPrepare_ok h.2.1.1 h.2.1.2.1 32 (by decide) (by decide) h.2.1.2.2.1 h.2.1.2.2.2⟩)
  have hm : CT (fun x y => MulCTPreN 32 base scalar x ∧ MulCTPreN 32 base scalar y)
      (pointMultiplyVar 32) (fun _ _ => True) := by
    refine pointMultiplyVar_ct_of_init 32 base scalar (by decide) (by decide) ?_
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.1.x0 h.2.1.x0
  rw [pointFromScalarVar]
  refine CT.seq hp' ?_
  intro s t ts tt s' t' ⟨hsp, _, a, b, hab, ha, hb⟩ es et
  refine hm _ _ _ _ _ _ ⟨hsp, ⟨ha.1.scratch hab.1.1.1, ?_, ha.2.2.1, ?_⟩,
    ⟨hb.1.scratch hab.2.1.1, ?_, hb.2.2.1, ?_⟩⟩ es et
  · rw [← hab.1.2]; exact ha.2.2.2.1
  · rw [← hab.1.2]; exact ha.2.2.2.2
  · rw [← hab.2.2]; exact hb.2.2.2.1
  · rw [← hab.2.2]; exact hb.2.2.2.2

theorem baseMulBatchVar_ct {s₁ s₂ : State} {base : Addr} {scalar j : Nat} (hj : j < 16) :
    CT (fun x y => BaseMulVarInv s₁ base scalar (j + 1) x ∧
      BaseMulVarInv s₂ base scalar (j + 1) y) baseMulBatchVar (fun _ _ => True) := by
  rw [baseMulBatchVar]
  refine seq_runs ?_ (fun x h => baseVarBegin_ok h) (fun y h => baseVarBegin_ok h) ?_
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  refine seq_runs ?_ (fun x h => baseVarTable_ok hj h) (fun y h => baseVarTable_ok hj h) ?_
  · apply CT.taint (Taint.ofRegs [.x0, .x19]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.scratch.x0.trans h.2.1.scratch.x0.symm
    · exact h.1.2.trans h.2.2.symm
  refine seq_runs ?_ (fun x h => baseVarOffset_ok hj h) (fun y h => baseVarOffset_ok hj h) ?_
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.1.scratch.x0 h.2.1.scratch.x0
  refine seq_runs ?_ (fun x h => baseVarAccumulate_ok hj h) (fun y h => baseVarAccumulate_ok hj h) ?_
  · exact (accumulateVar16_ct pointAddCached_spec addEntryCached_ct base (16 * j) scalar _ _
      (by omega)).mono (fun _ _ h => ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.scratch.x0 h.2.scratch.x0

theorem baseMulLoopVar_ct (s₁ s₂ : State) (base : Addr) (scalar : Nat) (n : Nat) :
    CT (fun x y => BaseMulVarInv s₁ base scalar n x ∧ BaseMulVarInv s₂ base scalar n y)
      (.loop baseMulBatchVar (.nonzero .x .x19)) (fun _ _ => True) := by
  apply CT.loop (fun n x y => BaseMulVarInv s₁ base scalar n x ∧ BaseMulVarInv s₂ base scalar n y) _ n
  intro k
  cases k with
  | zero =>
    apply CT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < 16
    · have hw := withRuns (baseMulBatchVar_ct (s₁ := s₁) (s₂ := s₂) (base := base) (scalar := scalar) hj)
        (fun x y h => ⟨baseMulBatchVar_ok hj h.1, baseMulBatchVar_ok hj h.2⟩)
      refine hw.mono (fun _ _ h => h) ?_
      intro x y ⟨_, a, b, _, ⟨hx, xz⟩, ⟨hy, yz⟩⟩
      have ex : eval (.nonzero .x .x19) x = some (decide (j ≠ 0)) := by
        simp only [eval, read_x, xz, batch_counter_nonzero j (by omega)]
      have ey : eval (.nonzero .x .x19) y = some (decide (j ≠ 0)) := by
        simp only [eval, read_x, yz, batch_counter_nonzero j (by omega)]
      refine ⟨ex.trans ey.symm, fun _ => trivial, fun he => ?_⟩
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp only [ex, show decide ((0 : Nat) ≠ 0) = false from rfl] at he
        cases he
      exact ⟨j, by omega, ⟨by omega, by omega, hx.scratch, hx.counter, hx.value, hx.bits, hx.d, hx.keep⟩,
        ⟨by omega, by omega, hy.scratch, hy.counter, hy.value, hy.bits, hy.d, hy.keep⟩⟩
    · apply CT.of_false
      intro x y h
      have := h.1.bound
      omega

theorem baseFromScalarVar_ct (base k : Addr) (scalar : Nat) :
    CT (fun s t => ScalarVarCTPre 16 base k scalar s ∧ ScalarVarCTPre 16 base k scalar t)
      baseFromScalarVar (fun _ _ => True) := by
  have hp : CT (fun s t => ScalarVarCTPre 16 base k scalar s ∧ ScalarVarCTPre 16 base k scalar t)
      (pointFromScalarPrepare 16) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1]) _ (by taint_decide)
    exact fun _ _ h => scalarInput_agree ⟨h.1.1, h.2.1⟩
  have hp' := withRuns hp (fun s t h =>
    ⟨pointFromScalarPrepare_ok h.1.1.1 h.1.1.2.1 16 (by decide) (by decide) h.1.1.2.2.1 h.1.1.2.2.2,
     pointFromScalarPrepare_ok h.2.1.1 h.2.1.2.1 16 (by decide) (by decide) h.2.1.2.2.1 h.2.1.2.2.2⟩)
  have hinit : CT (fun x y => MulCTPre base scalar x ∧ MulCTPre base scalar y)
      (.block baseMultiplyInit) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun x y h => x0_agree h.1.1.x0 h.2.1.x0
  have hi := withRuns hinit (fun x y h =>
    ⟨baseMultiplyVarInit_ok h.1.1 scalar h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     baseMultiplyVarInit_ok h.2.1 scalar h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  have hm : CT (fun x y => MulCTPre base scalar x ∧ MulCTPre base scalar y)
      baseMultiplyVar (fun _ _ => True) := by
    rw [baseMultiplyVar]
    refine CT.seq hi ?_
    intro x y tx ty x' y' ⟨hsp, _, a, b, _, hx, hy⟩ ex ey
    exact baseMulLoopVar_ct a b base scalar 16 _ _ _ _ _ _ ⟨hsp, hx, hy⟩ ex ey
  rw [baseFromScalarVar]
  refine CT.seq hp' ?_
  intro s t ts tt s' t' ⟨hsp, _, a, b, hab, ha, hb⟩ es et
  refine hm _ _ _ _ _ _ ⟨hsp, ⟨ha.1.scratch hab.1.1.1, ?_, ha.2.2.1, ?_⟩,
    ⟨hb.1.scratch hab.2.1.1, ?_, hb.2.2.1, ?_⟩⟩ es et
  · rw [← hab.1.2]; exact ha.2.2.2.1
  · rw [← hab.1.2]; exact ha.2.2.2.2
  · rw [← hab.2.2]; exact hb.2.2.2.1
  · rw [← hab.2.2]; exact hb.2.2.2.2

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.AArch64.BaseMultiplyLit
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCTBatch

/-!
# Base-point multiplication from the cached table has a public trace

Untrusted. The batch is chosen by the public counter `x19`, and every
address is a pointer plus a constant or a counter.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def BaseBatchCTPre (base : Addr) (j : Nat) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)

def BaseBatchCTReady (base : Addr) (j : Nat) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧ s.gpr .x19 = BitVec.ofNat 64 j

theorem baseBegin_ct (base : Addr) (j : Nat) :
    CT (fun x y => BaseBatchCTPre base j x ∧ BaseBatchCTPre base j y)
      (.block batchBegin) (fun x y => BaseBatchCTReady base j x ∧ BaseBatchCTReady base j y) := by
  apply both_wp
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  · intro s ⟨hs, hc⟩
    refine WP.mono (batchBegin_ok hs j hc) fun t ⟨tc, tv, tg, _, tw, _, _⟩ => ?_
    exact ⟨⟨(tg _ (by decide)).trans hs.x0, by rw [tw]; exact hs.wr, hs.nowrap⟩, tv, tc⟩

theorem baseBatchTable_ct (base : Addr) (j : Nat) (hj : j < 16) :
    CT (fun x y => BaseBatchCTReady base j x ∧ BaseBatchCTReady base j y)
      baseBatchTable (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y) := by
  apply both_wp
  · apply CT.taint (Taint.ofRegs [.x0, .x19]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.x0.trans h.2.1.x0.symm
    · exact h.1.2.2.trans h.2.2.2.symm
  · intro s ⟨hs, hc, hr⟩
    refine WP.mono (baseBatchTable_ok hs j hj hr) fun t ht => ?_
    exact ⟨ht.powersKeep.scratch hs, ((tableFrame_outside ht.powersKeep.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans hc⟩

theorem baseMulBatch_ct (base : Addr) (j : Nat) (hj : j < 16) :
    CT (fun x y => BaseBatchCTPre base j x ∧ BaseBatchCTPre base j y)
      baseMulBatch (fun _ _ => True) := by
  rw [baseMulBatch]
  refine CT.seq (baseBegin_ct base j) (CT.seq (baseBatchTable_ct base j hj)
    (CT.seq (offset_ct base j (by omega)) (CT.seq
      (R := fun (x y : State) => ∀ r ∈ ([.x0] : List Reg), x.gpr r = y.gpr r) ?_ ?_)))
  · apply CT.taintRegs (τ := Taint.ofRegs [.x0, .x1]) _ [.x0] (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs h

theorem baseMulLoop_ct (s₁ s₂ : State) (base : Addr) (scalar₁ scalar₂ : Nat) (n : Nat) :
    CT (fun x y => BaseMulInv s₁ base scalar₁ n x ∧ BaseMulInv s₂ base scalar₂ n y)
      (.loop baseMulBatch (.nonzero .x .x19)) (fun _ _ => True) := by
  apply CT.loop (fun n x y => BaseMulInv s₁ base scalar₁ n x ∧ BaseMulInv s₂ base scalar₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply CT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < 16
    · have hct := (baseMulBatch_ct base j hj).mono
        (fun x y (h : BaseMulInv s₁ base scalar₁ (j + 1) x ∧ BaseMulInv s₂ base scalar₂ (j + 1) y) =>
          ⟨⟨h.1.scratch, h.1.counter⟩, ⟨h.2.scratch, h.2.counter⟩⟩)
        (fun _ _ h => h)
      have hw := withRuns hct (fun x y h =>
        ⟨baseMulBatch_ok h.1.scratch j scalar₁ hj h.1.counter h.1.value h.1.bits,
         baseMulBatch_ok h.2.scratch j scalar₂ hj h.2.counter h.2.value h.2.bits⟩)
      refine hw.mono (fun _ _ h => h) ?_
      intro x y ⟨_, a, b, hi, hx, hy⟩
      have ex : eval (.nonzero .x .x19) x = some (decide (j ≠ 0)) := by
        simp only [eval, read_x, hx.2.1, batch_counter_nonzero j (by omega)]
      have ey : eval (.nonzero .x .x19) y = some (decide (j ≠ 0)) := by
        simp only [eval, read_x, hy.2.1, batch_counter_nonzero j (by omega)]
      refine ⟨ex.trans ey.symm, fun _ => trivial, ?_⟩
      intro he
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp only [ex, show decide ((0 : Nat) ≠ 0) = false from rfl] at he
        cases he
      refine ⟨j, by omega, ?_, ?_⟩
      · exact ⟨by omega, by omega, hx.2.2.2.2.scratch hi.1.scratch, hx.1, hx.2.2.1, hx.2.2.2.1,
          hi.1.keep.trans hx.2.2.2.2⟩
      · exact ⟨by omega, by omega, hy.2.2.2.2.scratch hi.2.scratch, hy.1, hy.2.2.1, hy.2.2.2.1,
          hi.2.keep.trans hy.2.2.2.2⟩
    · apply CT.of_false
      intro x y h
      have := h.1.bound
      omega

def BaseMulCTPre (base : Addr) (scalar : Nat) (s : State) : Prop :=
  Scr s base ∧ scalar < 2 ^ (16 * 16) ∧
    ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)

theorem baseMultiply_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    CT (fun x y => BaseMulCTPre base scalar₁ x ∧ BaseMulCTPre base scalar₂ y)
      baseMultiply (fun _ _ => True) := by
  have initCT : CT (fun x y => BaseMulCTPre base scalar₁ x ∧ BaseMulCTPre base scalar₂ y)
      (.block baseMultiplyInit) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  have hi := withRuns initCT (fun x y h =>
    ⟨baseMultiplyInit_ok h.1.1 scalar₁ h.1.2.1 h.1.2.2,
     baseMultiplyInit_ok h.2.1 scalar₂ h.2.2.1 h.2.2.2⟩)
  rw [baseMultiply]
  refine CT.seq hi ?_
  intro x y tx ty x' y' ⟨hsp, _, a, b, _, hx, hy⟩ ex ey
  exact baseMulLoop_ct a b base scalar₁ scalar₂ 16 _ _ _ _ _ _ ⟨hsp, hx, hy⟩ ex ey

end VG.Proof.Ed25519.AArch64

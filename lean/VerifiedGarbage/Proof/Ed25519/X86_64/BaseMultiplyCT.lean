import VerifiedGarbage.Proof.Ed25519.X86_64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseMultiplyLit
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCT

/-!
# Base-point multiplication from the cached table has a public trace

Untrusted. The batch is chosen by the public counter `rbx`, and every
address is a pointer plus a constant or a counter.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem baseBatchTable_ct (base : Addr) (j : Nat) (hj : j < 16) :
    RelCT isa (fun x y => BatchCTReady base j x ∧ BatchCTReady base j y)
      baseBatchTable (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y) := by
  apply both_wp
  · apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  · intro s ⟨hs, hc, _, hr⟩
    refine WP.mono (baseBatchTable_ok hs j hj hr) fun t ht => ?_
    exact ⟨ht.powersKeep.scratch hs, ((tableFrame_outside ht.powersKeep.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans hc⟩

theorem baseMulBatch_ct (base : Addr) (j : Nat) (hj : j < 16) :
    RelCT isa (fun x y => BatchCTPre base j x ∧ BatchCTPre base j y)
      (baseMulBatch fld) (fun _ _ => True) := by
  rw [baseMulBatch]
  refine VG.RelCT.seq (begin_ct base j) (VG.RelCT.seq (baseBatchTable_ct base j hj)
    (VG.RelCT.seq (offset_ct base j (by omega)) (VG.RelCT.seq
      (R := fun (x y : State) => ∀ r ∈ ([.rdi] : List Reg), x.gpr r = y.gpr r) ?_ ?_)))
  · apply taintRegsFld (τ := Taint.ofRegs [.rdi, .rsi]) _ [.rdi] (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs h

/-- The loop's invariant, with the curve constant that `BatchCTPre` asks for. -/
def BaseMulCTInv (s₀ : State) (base : Addr) (scalar n : Nat) (s : State) : Prop :=
  BaseMulInv s₀ base scalar n s ∧ env s₀.mem base 16 = Spec.Ed25519.d

theorem baseMulLoop_ct (s₁ s₂ : State) (base : Addr) (scalar₁ scalar₂ : Nat) (n : Nat) :
    RelCT isa (fun x y => BaseMulCTInv s₁ base scalar₁ n x ∧ BaseMulCTInv s₂ base scalar₂ n y)
      (.loop (baseMulBatch fld) .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (fun n x y => BaseMulCTInv s₁ base scalar₁ n x ∧
    BaseMulCTInv s₂ base scalar₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply VG.RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.1.positive
  | succ j =>
    by_cases hj : j < 16
    · have hct := (baseMulBatch_ct (fld := fld) base j hj).mono
        (fun x y (h : BaseMulCTInv s₁ base scalar₁ (j + 1) x ∧ BaseMulCTInv s₂ base scalar₂ (j + 1) y) =>
          ⟨⟨h.1.1.scratch, h.1.1.counter, h.1.1.slot16.trans h.1.2⟩,
           ⟨h.2.1.scratch, h.2.1.counter, h.2.1.slot16.trans h.2.2⟩⟩)
        (fun _ _ h => h)
      have hw := withRuns hct (fun x y h =>
        ⟨baseMulBatch_ok h.1.1.scratch j scalar₁ hj h.1.1.counter h.1.1.value h.1.1.bits,
         baseMulBatch_ok h.2.1.scratch j scalar₂ hj h.2.1.counter h.2.1.value h.2.1.bits⟩)
      refine hw.mono (fun _ _ h => h) ?_
      intro x y ⟨_, a, b, hi, hx, hy⟩
      have ex : eval .ne x = some (!(decide (j = 0))) := by
        simp only [eval, hx.2.1, Option.map_some]
      have ey : eval .ne y = some (!(decide (j = 0))) := by
        simp only [eval, hy.2.1, Option.map_some]
      refine ⟨ex.trans ey.symm, fun _ => trivial, ?_⟩
      intro he
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp only [ex, decide_true, Bool.not_true] at he
        cases he
      refine ⟨j, by omega, ⟨⟨by omega, by omega, hx.2.2.2.2.2.scratch hi.1.1.scratch, hx.1,
          hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1.trans hi.1.1.slot16, hi.1.1.keep.trans hx.2.2.2.2.2⟩, hi.1.2⟩,
        ⟨⟨by omega, by omega, hy.2.2.2.2.2.scratch hi.2.1.scratch, hy.1,
          hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1.trans hi.2.1.slot16, hi.2.1.keep.trans hy.2.2.2.2.2⟩, hi.2.2⟩⟩
    · apply VG.RelCT.of_false
      intro x y h
      have := h.1.1.bound
      omega

theorem baseMultiply_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (baseMultiply fld) (fun _ _ => True) := by
  have initCT : RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (.block (baseMultiplyInit fld)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  have hi := withRuns initCT (fun x y h =>
    ⟨baseMultiplyInit_ok h.1.1 scalar₁ h.1.2.1 h.1.2.2.2,
     baseMultiplyInit_ok h.2.1 scalar₂ h.2.2.1 h.2.2.2.2⟩)
  rw [baseMultiply]
  refine VG.RelCT.seq (hi.mono (fun _ _ h => h) (Q' := fun x y => ∃ x₀ y₀,
      BaseMulCTInv x₀ base scalar₁ 16 x ∧ BaseMulCTInv y₀ base scalar₂ 16 y) ?_) ?_
  · intro x y ⟨_, a, b, hab, hx, hy⟩
    exact ⟨x, y, ⟨⟨hx.positive, hx.bound, hx.scratch, hx.counter, hx.value, hx.bits, rfl,
      PowersKeep.refl _ _ _ _⟩, hx.slot16.trans hab.1.2.2.1⟩,
      ⟨⟨hy.positive, hy.bound, hy.scratch, hy.counter, hy.value, hy.bits, rfl,
      PowersKeep.refl _ _ _ _⟩, hy.slot16.trans hab.2.2.2.1⟩⟩
  · intro x y tx ty x' y' ⟨x₀, y₀, hx, hy⟩ ex ey
    exact baseMulLoop_ct x₀ y₀ base scalar₁ scalar₂ 16 _ _ _ _ _ _ ⟨hx, hy⟩ ex ey

end VG.Proof.Ed25519.X86_64

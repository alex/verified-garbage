import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulVar
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulVarLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Variable-time bit loops: what their traces depend on

Untrusted. The bit loop branches on the scalar's bits, so its trace depends
on the scalar: both runs must multiply by the same scalar (in verification,
the public inputs are the same in both runs). Everything else is public by
the taint analysis or, for the branches, by correctness.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps)

/-- Chains two programs whose runs each satisfy a predicate of their own. -/
theorem seq_runs {A₁ A₂ B₁ B₂ : State → Prop} {Q : State → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (fun x y => A₁ x ∧ A₂ y) c₁ (fun _ _ => True))
    (w₁ : ∀ x, A₁ x → WP isa c₁ x B₁) (w₂ : ∀ y, A₂ y → WP isa c₁ y B₂)
    (h₂ : RelCT isa (fun x y => B₁ x ∧ B₂ y) c₂ Q) :
    RelCT isa (fun x y => A₁ x ∧ A₂ y) (.seq c₁ c₂) Q :=
  VG.RelCT.seq ((VG.RelCT.wp h₁ fun x y h => ⟨w₁ x h.1, w₂ y h.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) h₂

/-- After the bit test: what the rest of the loop body's trace depends on. -/
def VarBitTested (base : Addr) (n bit : Nat) (s : State) : Prop :=
  s.gpr .rdi = base ∧ s.gpr .rbx = BitVec.ofNat 64 n ∧ s.zf = some (decide (bit = 0))

theorem varBitBlock_ok {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {s₀ s : State} {base : Addr}
    {start scalar n : Nat} {p : Spec.Ed25519.Point} (hi : start + 16 ≤ 512)
    (h : AccumulateVarInv f s₀ base start scalar p (n + 1) s) :
    WP isa (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ scalarBitTest)) s
      (VarBitTested base n ((scalar / 2 ^ (start + n)) % 2)) := by
  have hn : n < 16 := by have := h.bound; omega
  rw [WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n h.counter) fun a ⟨ac, ka⟩ => ?_
  refine WP.mono (scalarBitTest_ok (h.scratch.of_keeps ka (by decide)) n start
    ((scalar / 2 ^ (start + n)) % 2) (by omega) (by omega) ac
    ((ka.1 _ (by decide)).trans h.startReg) (by rw [ka.2.1]; exact h.bits n hn)) fun b ⟨bz, kb⟩ => ?_
  exact ⟨(kb.1 _ (by decide)).trans ((ka.1 _ (by decide)).trans h.scratch.rdi),
    (kb.1 _ (by decide)).trans ac, bz⟩

theorem accumulateVarBody_ct {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (addEntry add)) (fun _ _ => True))
    {s₁ s₂ : State} {base : Addr} {start scalar n : Nat} {p₁ p₂ : Spec.Ed25519.Point}
    (hi : start + 16 ≤ 512) :
    RelCT isa (fun x y => AccumulateVarInv f s₁ base start scalar p₁ (n + 1) x ∧
      AccumulateVarInv f s₂ base start scalar p₂ (n + 1) y) (accumulateVarBody add) (fun _ _ => True) := by
  rw [accumulateVarBody]
  refine seq_runs ?_ (fun x h => varBitBlock_ok hi h) (fun y h => varBitBlock_ok hi h) ?_
  · apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx, .rsi]) _ (by taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.scratch.rdi.trans h.2.scratch.rdi.symm
    · exact h.1.counter.trans h.2.counter.symm
    · exact h.1.startReg.trans h.2.startReg.symm
  · refine VG.RelCT.seq (R := fun _ _ => True) (VG.RelCT.ite ?_ ?_ ?_) ?_
    · intro x y h
      simp only [eval, h.1.2.2, h.2.2.2]
    · exact hadd.mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.1.trans h.1.2.2.1.symm⟩)
        (fun _ _ h => h)
    · exact VG.RelCT.block_nil (fun _ _ _ => trivial)
    · apply VG.RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      exact fun _ _ _ => Taint.agree_ofRegs (by simp)

theorem accumulateVarLoop_ct {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f)
    (hct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (addEntry add)) (fun _ _ => True))
    (s₁ s₂ : State) (base : Addr) (start scalar : Nat) (p₁ p₂ : Spec.Ed25519.Point)
    (hi : start + 16 ≤ 512) (n : Nat) :
    RelCT isa (fun x y => AccumulateVarInv f s₁ base start scalar p₁ n x ∧
      AccumulateVarInv f s₂ base start scalar p₂ n y) (.loop (accumulateVarBody add) .ne)
      (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (fun n x y => AccumulateVarInv f s₁ base start scalar p₁ n x ∧
    AccumulateVarInv f s₂ base start scalar p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply VG.RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    have hw := withRuns (accumulateVarBody_ct (f := f) (s₁ := s₁) (s₂ := s₂) (p₁ := p₁) (p₂ := p₂)
      (base := base) (start := start)
      (n := j) (scalar := scalar) hct hi)
      (fun x y h => ⟨accumulateVarStep_ok hadd hi h.1, accumulateVarStep_ok hadd hi h.2⟩)
    refine hw.mono (fun _ _ h => h) ?_
    intro x y ⟨_, a, b, _, hx, hy⟩
    have ex : eval .ne x = some (!(decide (j = 0))) := by simp only [eval, hx.1, Option.map_some]
    have ey : eval .ne y = some (!(decide (j = 0))) := by simp only [eval, hy.1, Option.map_some]
    refine ⟨ex.trans ey.symm, fun _ => trivial, fun he => ?_⟩
    have hj0 : j ≠ 0 := by
      intro hz
      subst j
      simp only [ex, decide_true, Bool.not_true] at he
      cases he
    exact ⟨j, by omega, hx.2.2.2.2 hj0, hy.2.2.2.2 hj0⟩

/-- Before a batch's bits: what `accumulateVar16`'s trace depends on. -/
def AccumulateVarPre (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (base : Addr) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = BitVec.ofNat 64 start ∧
    (∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)) ∧
    env s.mem base 16 = Spec.Ed25519.d ∧
    point (env s.mem base) 0 1 2 3 = after scalar p (start + 16) ∧
    (∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = f (powerPoint p (start + i)))

theorem accumulateVar16_ct {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f)
    (hct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (addEntry add)) (fun _ _ => True))
    (base : Addr) (start scalar : Nat) (p₁ p₂ : Spec.Ed25519.Point) (hi : start + 16 ≤ 512) :
    RelCT isa (fun x y => AccumulateVarPre f base start scalar p₁ x ∧
      AccumulateVarPre f base start scalar p₂ y) (accumulateVar16 add) (fun _ _ => True) := by
  rw [accumulateVar16]
  have init (x : State) (h : AccumulateVarPre f base start scalar p₁ x ∨
      AccumulateVarPre f base start scalar p₂ x) :
      WP isa (.block [.mov32 .rbx (.imm 16)]) x fun t => t.gpr .rbx = 16 ∧ Keeps [.rbx] x t :=
    accumulateInit_ok x
  refine VG.RelCT.seq ((VG.RelCT.wpDep (F := fun (x t : State) => t.gpr .rbx = 16 ∧ Keeps [.rbx] x t)
    (VG.RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (by taint_decide)) (fun x y h => ⟨init x (Or.inl h.1), init y (Or.inr h.2)⟩)).mono
    (fun _ _ h => h) (Q' := fun x' y' => ∃ x y, (AccumulateVarPre f base start scalar p₁ x ∧
      AccumulateVarPre f base start scalar p₂ y) ∧ AccumulateVarInv f x base start scalar p₁ 16 x' ∧
      AccumulateVarInv f y base start scalar p₂ 16 y') ?_) ?_
  · intro x' y' ⟨_, x, y, hxy, ⟨xc, xk⟩, ⟨yc, yk⟩⟩
    have mk : ∀ {p : Spec.Ed25519.Point} {s t : State}, AccumulateVarPre f base start scalar p s →
        t.gpr .rbx = 16 → Keeps [.rbx] s t → AccumulateVarInv f s base start scalar p 16 t :=
      fun h tc tk => ⟨by decide, by decide, h.1.of_keeps tk (by decide), tc,
        (tk.1 _ (by decide)).trans h.2.1, by rw [tk.2.1]; exact h.2.2.2.1,
        by rw [tk.2.1]; exact h.2.2.2.2.1, by rw [tk.2.1]; exact h.2.2.1,
        by rw [tk.2.1]; exact h.2.2.2.2.2, RbxKeep.of_keeps tk (by decide)⟩
    exact ⟨x, y, hxy, mk hxy.1 xc xk, mk hxy.2 yc yk⟩
  · intro x y tx ty x' y' ⟨x₀, y₀, _, hx, hy⟩ ex ey
    exact accumulateVarLoop_ct hadd hct x₀ y₀ base start scalar p₁ p₂ hi 16 _ _ _ _ _ _ ⟨hx, hy⟩ ex ey

theorem addEntryExact_ct :
    RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (addEntry pointAdd)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) _ (by taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem addEntryCached_ct :
    RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (addEntry pointAddCached)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) _ (by taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

end VG.Proof.Ed25519.X86_64

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa
import VerifiedGarbage.Proof.Scrypt.Spec

/-!
# The Salsa20/8 Core on AArch64: the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Scrypt.AArch64

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne_x1 {k : Nat} (hk : k < 16) : wreg k ≠ .x1 := by
  have key : ∀ k, k < 16 → wreg k ≠ .x1 := by decide
  exact key k hk

/-- The registers that hold words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

/-! ## One line, on registers -/

/-- `a ^= R(b + c)` through `w1`, rotating right by `sh`. -/
theorem line_regs {a b c : Reg} (ha : a ≠ .x1) {sh : Nat} (hsh : sh < 32) (s : State) (va vb vc : Word)
    (hva : s.gpr a = va.setWidth 64) (hvb : s.gpr b = vb.setWidth 64)
    (hvc : s.gpr c = vc.setWidth 64) :
    WP isa (.block [.add .w .x1 b c, .ror .w .x1 .x1 sh, .logic .eor .w a a .x1]) s fun s' =>
      s'.gpr a = (va ^^^ (vb + vc).rotateRight sh).setWidth 64 ∧
      (∀ r, r ≠ a → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_logic, exec_ror_w hsh, isa, State.read, State.write, Size.bits, hva, hvb, hvc, ha,
    ite_true, ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h1 h2 => ?_, trivial⟩
  simp only [h1, h2, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop :=
  ∀ k (hk : k < 16), s.gpr (wreg k) = v[k].setWidth 64

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  have ne : ∀ {a b}, a < 16 → b < 16 → a ≠ b → wreg a ≠ wreg b := fun ha hb hab e =>
    hab (wreg_inj ha hb e)
  refine WP.mono (line_regs (wreg_ne_x1 hi) (show 32 - n < 32 by omega) s _ _ _ (h.holds i hi) (h.holds j hj)
    (h.holds k hk)) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw hx => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, rotateLeft_eq _ (by omega) (by omega)]
    · simp only [e, ite_false]
      rw [hr _ (ne hm' hi (Ne.symm e)) (wreg_ne_x1 hm')]
      exact h.holds m hm'
  · rw [hr r (fun e => hw ⟨i, hi, e⟩) hx]
    exact h.keep r hw hx

/-! ## Double rounds -/

theorem lines_ok {s₀ : State} :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h) fun s' h' => lines_ok l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {v : Vector Word 16} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok lines (by decide) v s h

theorem rounds_ok {v : Vector Word 16} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.Scrypt.AArch64

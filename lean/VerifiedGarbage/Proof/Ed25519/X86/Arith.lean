import VerifiedGarbage.Proof.Ed25519.X86.Fold
import Mathlib.Tactic.Ring

/-!
# Ed25519 on x86 (32-bit): the field operations

Each operation of `Impl/X25519/X86.lean` on elements at offsets of the working
space, as the operation of `GF(p)` on their values modulo `p`: `mul` (by
product scanning into `T`, then `lo + 38 hi`), `add`, `sub` (as `a + (2²⁵⁶ - 1 -
b) + (2²⁵⁶ - 75)`), `mulSmall` (by 121665). Each leaves the rest of memory
unchanged but for the output and, for `mul`, `T`.
-/

namespace VG.Proof.Ed25519.X86

open VG.Proof.X25519
open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-! ## Numbers in any base, for `ring` -/

/-- `num` in any base. -/
def numB (B : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => numB B f n + B ^ n * f n

theorem num_eq_numB (f : Nat → Nat) (n : Nat) : num f n = numB (2 ^ 32) f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [num_succ, numB, ih]

/-- Product scanning: the columns of `a b` in radix `2³²`. -/
theorem prod_identity (fa fb : Nat → Nat) :
    num (fun k => (((List.range 8).filter fun i => i ≤ k && k - i < 8).map fun i =>
      fa i * fb (k - i)).sum) 16 = num fa 8 * num fb 8 := by
  simp only [num_eq_numB]
  generalize 2 ^ 32 = B
  simp only [numB, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil]
  simp (config := {decide := true}) only [ite_true, ite_false, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem num_16 (f : Nat → Nat) : num f 16 = num f 8 + 2 ^ 256 * num (fun k => f (8 + k)) 8 := by
  simp only [num_eq_numB]
  rw [show (2 : Nat) ^ 256 = (2 ^ 32) ^ 8 by rw [← Nat.pow_mul]]
  generalize 2 ^ 32 = B
  simp only [numB]
  ring

/-- The complements of the words. -/
theorem num_not {f : Nat → Nat} (h : ∀ k < 8, f k < 2 ^ 32) :
    num (fun k => 2 ^ 32 - 1 - f k) 8 = 2 ^ 256 - 1 - num f 8 := by
  have hs := num_add (fun k => 2 ^ 32 - 1 - f k) f 8
  have hc : num (fun k => 2 ^ 32 - 1 - f k + f k) 8 = num (fun _ => 2 ^ 32 - 1) 8 :=
    num_congr fun k hk => by have := h k hk; omega_using [this]
  have h1 : num (fun _ => 2 ^ 32 - 1) 8 = 2 ^ 256 - 1 := rfl
  omega_using [hs, hc, h1]

/-! ## Columns -/

theorem colv_le_len {m : Mem} {x : BitVec 32} {B : Nat} :
    ∀ {ts : List Term}, (∀ t ∈ ts, tval m x t ≤ B) → colv m x ts ≤ ts.length * B
  | [], _ => by simp [colv]
  | t :: ts, h => by
    have h1 := h t List.mem_cons_self
    have h2 := colv_le_len (ts := ts) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [colv, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    rw [Nat.add_mul, Nat.one_mul]; omega_using [h1, h2]

theorem wv_lt (m : Mem) (x : BitVec 32) (d : Nat) : wv m x d < 2 ^ 32 := BitVec.isLt _

theorem wv_mul_le (m : Mem) (x : BitVec 32) (a b : Nat) : wv m x a * wv m x b ≤ 2 ^ 64 := by
  have h1 := wv_lt m x a; have h2 := wv_lt m x b
  exact Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt h1) (Nat.le_of_lt h2)) (by decide)

/-- Three offsets of elements, each either equal to or apart from the other. -/
def Apart (o a : Nat) : Prop := a = o ∨ a + 32 ≤ o ∨ o + 32 ≤ a

instance (o a : Nat) : Decidable (Apart o a) := inferInstanceAs (Decidable (a = o ∨ a + 32 ≤ o ∨ o + 32 ≤ a))

/-- The words of `[a]` a column `k` of an output at `o` reads. -/
theorem apart_read {o a k j : Nat} (h : Apart o a) (hk : k ≤ j) (hj : j < 8) :
    a + 4 * j + 4 ≤ o ∨ o + 4 * k ≤ a + 4 * j := by
  rcases h with h | h | h <;> omega_using [h, hk, hj]

/-! ## The operations -/

theorem zeroAcc_ok {s : State} :
    WP isa (.block zeroAcc) s fun s' => Keep s s' ∧ s'.mem = s.mem ∧ acc s' = 0 := by
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  refine ⟨(updKeep u₁).trans ((updKeep u₂).trans (updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  simp only [acc, v, u₃.gpr, u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.gpr,
    u₂.other .ebx (by decide), u₁.gpr, toNat_zero32]

/-- The offsets the arithmetic uses: elements below `T`. -/
def Below (o : Nat) : Prop := o + 32 ≤ T

instance : DecidablePred Below := fun o => inferInstanceAs (Decidable (o + 32 ≤ T))

theorem mul_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o a b : Nat} (ho : Below o) (ha : Below a)
    (hb : Below b) :
    WP isa (.block (mul o a b)) s fun s' => Keep s s' ∧ Frame [sub x o 32, sub x T 64] s.mem s'.mem ∧
      fe s'.mem x o % P = fe s.mem x a * fe s.mem x b % P := by
  simp only [Below, T] at ho ha hb
  have hfit := hc.fit
  refine WP.block_append (WP.block_append (WP.mono zeroAcc_ok fun s₁ ⟨k₁, m₁, a₁⟩ => ?_))
  have c₁ := k₁.ctx hc
  have hcol : ∀ k, colv s₁.mem x (prodTerms a b k) = (((List.range 8).filter fun i => i ≤ k && k - i < 8).map
      fun i => wv s.mem x (a + 4 * i) * wv s.mem x (b + 4 * (k - i))).sum := fun k => by
    simp only [colv, prodTerms, List.map_map, m₁]; rfl
  refine WP.mono (cols_ok c₁ (prodTerms a b) 16 (by simp only [T]; decide) (fun k hk t ht d hd => ?_)
    (fun k hk => ?_) (by rw [a₁]; decide)) fun s₂ ⟨k₂, f₂, e₂, _⟩ => ?_
  · simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at ht
    obtain ⟨i, ⟨hi, -, hki⟩, rfl⟩ := ht
    simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
    simp only [T]
    rcases hd with rfl | rfl <;> exact ⟨by omega_using [ha, hb, hi, hki], .inl (by omega_using [ha, hb, hi, hki])⟩
  · have hl : (prodTerms a b k).length ≤ 8 := by
      simp only [prodTerms, List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    have h1 := colv_le_len (m := s₁.mem) (x := x) (B := 2 ^ 64) (ts := prodTerms a b k) fun t ht => by
      simp only [prodTerms, List.mem_map] at ht
      obtain ⟨i, -, rfl⟩ := ht
      exact wv_mul_le _ _ _ _
    have h2 := Nat.mul_le_mul_right (2 ^ 64) hl
    omega_using [h1, h2]
  · -- The product, in `T`.
    rw [a₁, Nat.zero_add] at e₂
    simp only [hcol] at e₂
    rw [prod_identity (fun i => wv s.mem x (a + 4 * i)) (fun j => wv s.mem x (b + 4 * j))] at e₂
    change _ = fe s.mem x a * fe s.mem x b at e₂
    have hA := fe_lt s.mem x a; have hB := fe_lt s.mem x b
    have hAB : fe s.mem x a * fe s.mem x b < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul_of_lt_of_lt hA hB
    have e₃ : num (fun k => wv s₂.mem x (T + 4 * k)) 16 = fe s.mem x a * fe s.mem x b := by
      have hQ : ((2 : Nat) ^ 32) ^ 16 = 2 ^ 256 * 2 ^ 256 := by decide
      rw [hQ] at e₂
      have : acc s₂ = 0 := by
        rcases Nat.eq_zero_or_pos (acc s₂) with h | h
        · exact h
        · have := Nat.mul_le_mul_left (2 ^ 256 * 2 ^ 256) h
          omega_using [this, e₂, hAB]
      rw [this, Nat.mul_zero, Nat.add_zero] at e₂
      exact e₂
    rw [num_16] at e₃
    have c₂ := k₂.ctx c₁
    have hs : num (fun k => colv s₂.mem x [.mulI (T + 32 + 4 * k) 38, .addM (T + 4 * k)]) 8 =
        num (fun k => wv s₂.mem x (T + 4 * k)) 8 + 38 * num (fun k => wv s₂.mem x (T + 4 * (8 + k))) 8 := by
      rw [← num_mul, ← num_add]
      refine num_congr fun k _ => ?_
      show colv s₂.mem x _ = wv s₂.mem x (T + 4 * k) + 38 * wv s₂.mem x (T + 4 * (8 + k))
      rw [show T + 4 * (8 + k) = T + 32 + 4 * k by omega_using []]
      simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        toNat_38]
      omega_using []
    refine WP.mono (linear_ok c₂ o (fun k => [.mulI (T + 32 + 4 * k) 38, .addM (T + 4 * k)])
      (by omega_using [ho]) (fun k hk t ht d hd => ?_) (fun k hk => ?_) ?_) fun s₃ ⟨k₃, f₃, e₄⟩ =>
        ⟨k₁.trans (k₂.trans k₃), ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp only [treads, List.mem_singleton] at hd <;> subst hd <;>
        simp only [T] <;> exact ⟨by omega_using [hk], .inr (by omega_using [ho, hk])⟩
    · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, toNat_38]
      have h1 := wv_lt s₂.mem x (T + 32 + 4 * k); have h2 := wv_lt s₂.mem x (T + 4 * k)
      omega_using [h1, h2]
    · have hl := num_lt (f := fun k => wv s₂.mem x (T + 4 * k)) (n := 8) fun _ _ => wv_lt _ _ _
      have hh := num_lt (f := fun k => wv s₂.mem x (T + 4 * (8 + k))) (n := 8) fun _ _ => wv_lt _ _ _
      rw [hs]
      omega_using [hl, hh]
    · rw [m₁] at f₂
      exact (f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
        (f₃.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
    · rw [e₄, hs, ← fold256, ← e₃]

/-- The reads of a column `k` of an output at `o` from `[a + 4k]`. -/
theorem read_ok {o a k : Nat} (h : Apart o a) (ha : Below a) (hk : k < 8) :
    a + 4 * k + 4 ≤ 8192 ∧ (a + 4 * k + 4 ≤ o ∨ o + 4 * k ≤ a + 4 * k) :=
  ⟨by simp only [Below, T] at ha; omega_using [ha, hk], apart_read h (Nat.le_refl _) hk⟩

theorem add_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o a b : Nat} (ho : Below o) (ha : Below a)
    (hb : Below b) (hoa : Apart o a) (hob : Apart o b) :
    WP isa (.block (add o a b)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o % P = (fe s.mem x a + fe s.mem x b) % P := by
  have hs : num (fun k => colv s.mem x [.addM (a + 4 * k), .addM (b + 4 * k)]) 8 =
      fe s.mem x a + fe s.mem x b := by
    rw [fe, fe, ← num_add]
    refine num_congr fun k _ => ?_
    simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  refine WP.mono (linear_ok hc o _ (by simp only [Below, T] at ho; omega_using [ho])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) ?_) fun s' ⟨k', f', e'⟩ => ⟨k', f', by rw [e', hs]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp only [treads, List.mem_singleton] at hd <;> subst hd
    exacts [read_ok hoa ha hk, read_ok hob hb hk]
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := wv_lt s.mem x (a + 4 * k); have h2 := wv_lt s.mem x (b + 4 * k)
    omega_using [h1, h2]
  · rw [hs]; have h1 := fe_lt s.mem x a; have h2 := fe_lt s.mem x b; omega_using [h1, h2]

theorem num_subK : num (fun k => (subK k).toNat) 8 = 2 ^ 256 - 75 := by decide

theorem sub_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o a b : Nat} (ho : Below o) (ha : Below a)
    (hb : Below b) (hoa : Apart o a) (hob : Apart o b) :
    WP isa (.block (Impl.X25519.X86.sub o a b)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      (fe s'.mem x o + fe s.mem x b) % P = fe s.mem x a % P := by
  have hB := fe_lt s.mem x b
  have hs : num (fun k => colv s.mem x [.addM (a + 4 * k), .addNot (b + 4 * k), .addI (subK k)]) 8 =
      fe s.mem x a + (2 ^ 256 - 1 - fe s.mem x b) + (2 ^ 256 - 75) := by
    rw [fe, fe, ← num_subK, ← num_not fun k _ => wv_lt s.mem x (b + 4 * k), ← num_add, ← num_add]
    refine num_congr fun k _ => ?_
    simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.add_assoc]
  refine WP.mono (linear_ok hc o _ (by simp only [Below, T] at ho; omega_using [ho])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) ?_) fun s' ⟨k', f', e'⟩ => ⟨k', f', ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp only [treads, List.mem_singleton, List.not_mem_nil] at hd
    · subst hd; exact read_ok hoa ha hk
    · subst hd; exact read_ok hob hb hk
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := wv_lt s.mem x (a + 4 * k); have h3 := (subK k).isLt
    omega_using [h1, h3]
  · rw [hs]; have h1 := fe_lt s.mem x a; omega_using [h1, hB]
  · rw [Nat.add_mod, e', hs, ← Nat.add_mod]
    have e : fe s.mem x a + (2 ^ 256 - 1 - fe s.mem x b) + (2 ^ 256 - 75) + fe s.mem x b =
        fe s.mem x a + P * 4 := by simp only [P]; omega_using [hB]
    rw [e, Nat.add_mul_mod_self_left]

theorem mulSmall_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o a : Nat} (ho : Below o) (ha : Below a)
    (hoa : Apart o a) :
    WP isa (.block (mulSmall o a)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o % P = 121665 * fe s.mem x a % P := by
  have hs : num (fun k => colv s.mem x [.mulI (a + 4 * k) 121665]) 8 = 121665 * fe s.mem x a := by
    rw [fe, ← num_mul]
    refine num_congr fun k _ => ?_
    simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.mul_comm (wv _ _ _)]
    rfl
  refine WP.mono (linear_ok hc o _ (by simp only [Below, T] at ho; omega_using [ho])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) ?_) fun s' ⟨k', f', e'⟩ => ⟨k', f', by rw [e', hs]⟩
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact read_ok hoa ha hk
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := wv_lt s.mem x (a + 4 * k)
    have : wv s.mem x (a + 4 * k) * (121665 : BitVec 32).toNat ≤ 2 ^ 32 * 121665 :=
      Nat.mul_le_mul (Nat.le_of_lt h1) (by decide)
    omega_using [this]
  · rw [hs]; have h1 := fe_lt s.mem x a; omega_using [h1]

end VG.Proof.Ed25519.X86

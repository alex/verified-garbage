import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Finish
import VerifiedGarbage.Proof.Framework.Range

/-!
# The start of a product: operands in registers, constants, operand sums

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem A_inj : ∀ i < 8, ∀ j < 8, i ≠ j → Mul.A i ≠ Mul.A j := by decide

theorem A_mem : ∀ i < 8, Mul.A i ∈ [Reg.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9] := by decide

def aRegs : List Reg := [.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9]

theorem loadA_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a + 64 ≤ 8192)
    (ha8 : a % 8 = 0) :
    WP isa (.block (loadA a)) s fun t =>
      (∀ i < 8, t.gpr (Mul.A i) = word s.mem base (a + 8 * i)) ∧ t.mem = s.mem ∧
      Keeps aRegs s t := by
  have e : loadA a = (List.range 8).flatMap fun i => [ld (Mul.A i) (a + 8 * i)] := by
    simp only [loadA]
    rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (Mul.A i) = word s.mem base (a + 8 * i)) ∧ t.mem = s.mem ∧ Keeps aRegs s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (ld_ok ts (Mul.A n) (d := a + 8 * n) (by omega) (by omega)) fun u ⟨uv, um, uk⟩ => ?_
  refine ⟨fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [uv, tm]
    · have hne : Mul.A i ∉ [Mul.A n] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact A_inj i (by omega) n hn h
      rw [uk.1 _ hne, tv i (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact A_mem n hn

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun t =>
      t.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) ∧ t.gpr ZERO = 0 ∧ t.mem = s.mem ∧
      Keeps [MASK, ZERO] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide,
      show 16 * 2 < 64 from by decide, show 16 * 3 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [MASK, ZERO, State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [ZERO, RegUpd.gpr_write, ite_true]
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem add_ok (s : State) (d n m : Reg) :
    WP isa (.block [.add .x d n m]) s fun t =>
      t.gpr d = s.gpr n + s.gpr m ∧ t.mem = s.mem ∧ Keeps [d] s t := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, read_x, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_write, hq, ite_false]

theorem stw_ok {t : State} {base : Addr} (ht : Scr t base) (r : Reg) {d : Nat} (h8 : d % 8 = 0)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [st r d]) t fun t' =>
      (∀ d', d' + 8 ≤ 8192 → (d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') →
        word t'.mem base d' = if d' = d then t.gpr r else word t.mem base d') ∧
      Outside base d 8 t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine WP.mono (st_ok ht r h8 hd) fun t' ⟨hm, hk⟩ => ⟨fun d' hd' hs => ?_, ?_, ?_, hk.2.1, hk.2.2⟩
  · rw [hm]; exact word_writeW _ _ hd hd' hs _
  · rw [hm]; exact writeW_outside _ _ _ hd
  · funext q; exact hk.1 q (by simp)

theorem A_ne : ∀ i < 8, Mul.A i ∉ [Reg.x10, .x11, .x13] := by decide

/-- One step of the operand sums of a product. -/
theorem kakbStep_ok {s : State} {base : Addr} (hs : Scr s base) {b i : Nat} (hb : b + 64 ≤ ACC)
    (hb8 : b % 8 = 0) (hi : i < 4) :
    WP isa (.block [.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      ld Mul.R.t (b + 8 * i), ld Mul.R.p1 (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)]) s fun t =>
      word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4)) ∧
      word t.mem base (KB + 8 * i) = word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i) ∧
      Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t ∧
      (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KA + 8 * i ∨ KA + 8 * i + 8 ≤ d) →
        (d + 8 ≤ KB + 8 * i ∨ KB + 8 * i + 8 ≤ d) → word t.mem base d = word s.mem base d) := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = ACC := rfl
  have hKB : KB = ACC + 32 := rfl
  rw [show [Instr.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      ld Mul.R.t (b + 8 * i), ld Mul.R.p1 (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)] =
      [Instr.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4))] ++ [st Mul.R.p0 (KA + 8 * i)] ++
      [ld Mul.R.t (b + 8 * i)] ++ [ld Mul.R.p1 (b + 32 + 8 * i)] ++
      [Instr.add .x Mul.R.t Mul.R.t Mul.R.p1] ++ [st Mul.R.t (KB + 8 * i)] from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (add_ok s _ _ _) fun t1 ⟨v1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stw_ok s1 _ (d := KA + 8 * i) (by omega) (by omega)) fun t2 ⟨w2, o2, g2, r2, wr2⟩ => ?_
  have s2 : Scr t2 base := ⟨by rw [g2]; exact s1.x3, by rw [g2]; exact s1.mask, wr2 ▸ s1.wr, s1.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok s2 Mul.R.t (d := b + 8 * i) (by omega) (by omega)) fun t3 ⟨v3, m3, k3⟩ => ?_
  have s3 : Scr t3 base := s2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok s3 Mul.R.p1 (d := b + 32 + 8 * i) (by omega) (by omega)) fun t4 ⟨v4, m4, k4⟩ => ?_
  have s4 : Scr t4 base := s3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_ok t4 _ _ _) fun t5 ⟨v5, m5, k5⟩ => ?_
  have s5 : Scr t5 base := s4.of_keeps k5 (by decide)
  refine WP.mono (stw_ok s5 _ (d := KB + 8 * i) (by omega) (by omega)) fun t6 ⟨w6, o6, g6, r6, wr6⟩ => ?_
  have hb1 : word t2.mem base (b + 8 * i) = word s.mem base (b + 8 * i) := by
    rw [w2 _ (by omega) (by omega), ite_eq_right (by omega), m1]
  have hb2 : word t2.mem base (b + 32 + 8 * i) = word s.mem base (b + 32 + 8 * i) := by
    rw [w2 _ (by omega) (by omega), ite_eq_right (by omega), m1]
  refine ⟨?_, ?_, ?_, ?_, fun d hd h1 h2 => ?_⟩
  · rw [w6 _ (by omega) (by omega), ite_eq_right (by omega), m5, m4, m3, w2 _ (by omega) (by omega),
      ite_eq_left rfl, v1]
  · rw [w6 _ (by omega) (by omega), ite_eq_left rfl, v5, k4.1 Mul.R.t (by decide), v3, v4, m3, hb1, hb2]
  · rw [← m1]
    refine (o2.mono (by omega) (by omega)).trans ?_
    rw [← m3, ← m4, ← m5]
    exact o6.mono (by omega) (by omega)
  · refine ⟨fun q hq => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [g6, k5.1 q (by simp [Mul.R, hq.1]), k4.1 q (by simp [Mul.R, hq.2.1]),
        k3.1 q (by simp [Mul.R, hq.1]), g2, k1.1 q (by simp [Mul.R, hq.2.2])]
    · rw [r6, k5.2.1, k4.2.1, k3.2.1, r2, k1.2.1]
    · rw [wr6, k5.2.2, k4.2.2, k3.2.2, wr2, k1.2.2]
  · rw [w6 _ hd (by omega), ite_eq_right (by omega), m5, m4, m3, w2 _ hd (by omega),
      ite_eq_right (by omega), m1]

end VG.Proof.Curve448.AArch64.Fast

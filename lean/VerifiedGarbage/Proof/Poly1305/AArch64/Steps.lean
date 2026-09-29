import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Poly1305.AArch64.Arith
import VerifiedGarbage.Impl.Poly1305.AArch64
import Mathlib.Tactic.NormNum.Basic

/-!
# Poly1305 on AArch64: the steps of the code

Untrusted: everything here is checked by Lean. Each lemma runs a few
instructions symbolically and states their effect on the numbers in the
registers, unconditionally (modulo `2⁶⁴` where the code wraps).
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64

/-- Two states agree except on the registers `rs`, in memory and regions. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂)
    (h₂ : Keeps rs' s₂ s₃) : Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem not_mem2 {a b c : Reg} (h₁ : a ≠ b) (h₂ : a ≠ c) : a ∉ [b, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h₁, h₂⟩

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-! ## Instructions -/

theorem exec_lsl_x {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) := by
  simp [exec, Size.bits, h]

theorem exec_madd {sz : Size} {s : State} {d n m a : Reg} :
    exec (.madd sz d n m a) s = some (s.write sz d (s.read sz a + s.read sz n * s.read sz m)) := rfl

theorem exec_mul {sz : Size} {s : State} {d n m : Reg} :
    exec (.mul sz d n m) s = some (s.write sz d (s.read sz n * s.read sz m)) := rfl

theorem write_gpr (s : State) (d : Reg) (x : BitVec 64) (r : Reg) :
    (s.write .x d x).gpr r = if r = d then x else s.gpr r := rfl

theorem write_gpr_w (s : State) (d : Reg) (x : BitVec 32) (r : Reg) :
    (s.write .w d x).gpr r = if r = d then x.setWidth 64 else s.gpr r := rfl

/-! ## Numbers -/

/-- The mask `2²⁶ - 1`. -/
abbrev M26 : BitVec 64 := 0x3ffffff

theorem and_mask (a : BitVec 64) : (a &&& M26).toNat = a.toNat % 2 ^ 26 := by
  rw [BitVec.toNat_and, show M26.toNat = 2 ^ 26 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem lsr_toNat (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lsl_toNat (a : BitVec 64) (n : Nat) : (a <<< n).toNat = a.toNat * 2 ^ n % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem add_toNat (a b : BitVec 64) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 :=
  BitVec.toNat_add a b

theorem madd_toNat (a b c : BitVec 64) :
    (a + b * c).toNat = (a.toNat + b.toNat * c.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod_mod]

set_option simprocs false in
/-- `2²⁶ - 1` into `x17`. -/
theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' => s'.gpr .x17 = M26 ∧ Keeps [.x17] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mask, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.write, Size.bits, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp [hr]

set_option simprocs false in
/-- The limbs of `lo + 2⁶⁴ hi` (in `x14, x15`) into `x9`–`x13`. -/
theorem split_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block split) s fun s' =>
      v s' .x9 = lim (v s .x14 + 2 ^ 64 * v s .x15) 0 ∧
      v s' .x10 = lim (v s .x14 + 2 ^ 64 * v s .x15) 1 ∧
      v s' .x11 = lim (v s .x14 + 2 ^ 64 * v s .x15) 2 ∧
      v s' .x12 = lim (v s .x14 + 2 ^ 64 * v s .x15) 3 ∧
      v s' .x13 = lim (v s .x14 + 2 ^ 64 * v s .x15) 4 ∧
      Keeps [.x9, .x10, .x11, .x12, .x13, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [split, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_lsr_x (show 52 < 64 by decide),
    exec_lsr_x (show 14 < 64 by decide), exec_lsr_x (show 40 < 64 by decide),
    exec_lsl_x (show 12 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  obtain ⟨a0, a1, a2, a3, a4⟩ := split_arith (v s .x14) (v s .x15) (s.gpr .x14).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hm, and_mask, ← a0]
  · rw [hm, and_mask, lsr_toNat, ← a1]
  · rw [hm, and_mask, add_toNat, lsr_toNat, lsl_toNat, ← a2]
  · rw [hm, and_mask, lsr_toNat, ← a3]
  · rw [lsr_toNat, ← a4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-! ## Sums of products -/

/-- The 32-bit word at `[x0 + off]`, as a number. -/
abbrev word (s : State) (off : Nat) : Nat := (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 32).toNat

theorem ldrw_toNat (m : Mem) (a : Addr) : ((m.readW a 32).setWidth 64).toNat = (m.readW a 32).toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans (m.readW a 32).isLt (by norm_num))]

set_option simprocs false in
/-- `d = h · c`, the coefficient `c` loaded into `x14`. -/
theorem mul1_ok (s : State) {d h : Reg} {off : Nat} (hh : h ≠ Reg.x14)
    (ho : off % 4 = 0 ∧ off < 16384) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.ldr .w .x14 .x0 off, .mul .x d h .x14]) s fun s' =>
      v s' d = v s h * word s off % 2 ^ 64 ∧ Keeps [.x14, d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_w ho hin, exec_mul, v, word, write_gpr, write_gpr_w,
    State.read, Size.bits, BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left', hh,
    ite_false]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_mul, ldrw_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, write_gpr_w, hr.1, hr.2, ite_false]

set_option simprocs false in
/-- `d += h · c`, the coefficient `c` loaded into `x14`. -/
theorem mac_ok (s : State) {d h : Reg} {off : Nat} (hh : h ≠ Reg.x14)
    (hd' : d ≠ Reg.x14) (ho : off % 4 = 0 ∧ off < 16384)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (mac d h off)) s fun s' =>
      v s' d = (v s d + v s h * word s off) % 2 ^ 64 ∧ Keeps [.x14, d] s s' := by
  apply WP.of_runBlock
  simp only [mac, runBlock_cons, runStep_some, runBlock_nil, exec_ldr_w ho hin, exec_madd, v, word,
    write_gpr, write_gpr_w, State.read, Size.bits, BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left',
    hh, hd', ite_false]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [madd_toNat, ldrw_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, write_gpr_w, hr.1, hr.2, ite_false]

/-- A chain of `mac`s. -/
theorem macs_ok {d : Reg} (L : List (Reg × Nat)) (s : State) (hd : Reg.x14 ≠ d) (hd0 : Reg.x0 ≠ d)
    (hL : ∀ p ∈ L, p.1 ≠ Reg.x14 ∧ p.1 ≠ d ∧ (p.2 % 4 = 0 ∧ p.2 < 16384) ∧
      InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 p.2) 4) :
    WP isa (.block (L.flatMap fun p => mac d p.1 p.2)) s fun s' =>
      v s' d = (v s d + (L.map fun p => v s p.1 * word s p.2).sum) % 2 ^ 64 ∧ Keeps [.x14, d] s s' := by
  induction L generalizing s with
  | nil =>
    refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (s.gpr d).isLt).symm
  | cons p L ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hL p List.mem_cons_self
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (mac_ok s h1 (Ne.symm hd) h3 h4) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.1 _ (not_mem2 (by decide) hd0)
    have hL' : ∀ q ∈ L, q.1 ≠ Reg.x14 ∧ q.1 ≠ d ∧ (q.2 % 4 = 0 ∧ q.2 < 16384) ∧
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0 + BitVec.ofNat 64 q.2) 4 := by
      intro q hq
      obtain ⟨g1, g2, g3, g4⟩ := hL q (List.mem_cons_of_mem _ hq)
      exact ⟨g1, g2, g3, by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact g4⟩
    refine WP.mono (ih s₁ hL') fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp)⟩
    have hw : (L.map fun q => v s₁ q.1 * word s₁ q.2) = (L.map fun q => v s q.1 * word s q.2) := by
      refine List.map_congr_left fun q hq => ?_
      obtain ⟨g1, g2, -, -⟩ := hL q (List.mem_cons_of_mem _ hq)
      simp only [v, word, x0₁, k₁.2.1, k₁.1 q.1 (not_mem2 g1 g2)]
    rw [e₂, hw, e₁, List.map_cons, List.sum_cons]
    omega


theorem dsum_facts : ∀ k < 5, Reg.x14 ≠ D.getD k .x9 ∧ Reg.x0 ≠ D.getD k .x9 ∧
    (coef k 0 % 4 = 0 ∧ coef k 0 < 16384) ∧ 72 ≤ coef k 0 ∧ coef k 0 + 4 ≤ 108 ∧
    ∀ i < 4, H.getD (i + 1) .x4 ≠ Reg.x14 ∧ H.getD (i + 1) .x4 ≠ D.getD k .x9 ∧
      (coef k (i + 1) % 4 = 0 ∧ coef k (i + 1) < 16384) ∧ 72 ≤ coef k (i + 1) ∧
      coef k (i + 1) + 4 ≤ 108 := by
  decide

/-- `dk = Σ hi · coef k i`. -/
theorem dsum_ok (s : State) {k : Nat} (hk : k < 5)
    (hc : ∀ off, 72 ≤ off → off + 4 ≤ 108 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (dsum k)) s fun s' =>
      v s' (D.getD k .x9) = (v s .x4 * word s (coef k 0) +
        ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * word s (coef k (i + 1))).sum) % 2 ^ 64 ∧
      Keeps [.x14, D.getD k .x9] s s' := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := dsum_facts k hk
  rw [dsum, show ((List.range 4).flatMap fun i => mac (D.getD k .x9) (H.getD (i + 1) .x4) (coef k (i + 1))) =
      (((List.range 4).map fun i => (H.getD (i + 1) .x4, coef k (i + 1))).flatMap fun p =>
        mac (D.getD k .x9) p.1 p.2) by rw [List.flatMap_map]]
  refine WP.block_append (WP.mono (mul1_ok s (by decide) f3 (hc _ f4 f5)) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.1 _ (not_mem2 (by decide) f2)
  have hL : ∀ p ∈ ((List.range 4).map fun i => (H.getD (i + 1) .x4, coef k (i + 1))),
      p.1 ≠ Reg.x14 ∧ p.1 ≠ D.getD k .x9 ∧ (p.2 % 4 = 0 ∧ p.2 < 16384) ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0 + BitVec.ofNat 64 p.2) 4 := by
    intro p hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    obtain ⟨g1, g2, g3, g4, g5⟩ := f6 i hi
    exact ⟨g1, g2, g3, by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact hc _ g4 g5⟩
  refine WP.mono (macs_ok _ s₁ f1 f2 hL) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp)⟩
  have hw : (((List.range 4).map fun i => (H.getD (i + 1) .x4, coef k (i + 1))).map fun p =>
      v s₁ p.1 * word s₁ p.2) = ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * word s (coef k (i + 1))) := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨g1, g2, -⟩ := f6 i (List.mem_range.mp hi)
    simp only [Function.comp_apply, v, word, x0₁, k₁.2.1, k₁.1 _ (not_mem2 g1 g2)]
  rw [e₂, hw, e₁, Nat.mod_add_mod]

set_option simprocs false in
/-- The carries of `absorb`, from `d0, …, d4` (in `x9`–`x13`) to the new limbs (in `x4`–`x8`). -/
theorem carry_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block carry) s fun s' =>
      (v s .x9 < 2 ^ 60 → v s .x10 < 2 ^ 60 → v s .x11 < 2 ^ 60 → v s .x12 < 2 ^ 60 →
        v s .x13 < 2 ^ 60 →
        val5 (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8) % Spec.Poly1305.P =
          val5 (v s .x9) (v s .x10) (v s .x11) (v s .x12) (v s .x13) % Spec.Poly1305.P ∧
        v s' .x4 < 2 ^ 26 ∧ v s' .x5 < 2 ^ 27 ∧ v s' .x6 < 2 ^ 26 ∧ v s' .x7 < 2 ^ 26 ∧
        v s' .x8 < 2 ^ 26) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [carry, carryStep, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_lsl_x (show 2 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat, lsl_toNat]
    obtain ⟨e, c0, c1, c2, c3, c4⟩ := carry_arith b0 b1 b2 b3 b4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
    refine ⟨?_, c0, c1, c2, c3, c4⟩
    rw [← e, Nat.add_mul_mod_self_left]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2]

set_option simprocs false in
/-- The two words at `[n + off]` into `x14, x15`. -/
theorem load2_ok (s : State) {n : Reg} {off : Nat} (hn : n ≠ Reg.x14)
    (ho : off % 8 = 0 ∧ off < 32768) (ho' : (off + 8) % 8 = 0 ∧ off + 8 < 32768)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 (off + 8)) 8) :
    WP isa (.block (load2 n off)) s fun s' =>
      s'.gpr .x14 = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧
      s'.gpr .x15 = s.mem.readW (s.gpr n + BitVec.ofNat 64 (off + 8)) 64 ∧ Keeps [.x14, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [load2, runBlock_cons, runStep_some,
    exec_ldr_x ho h0, State.write, Size.bits, BitVec.setWidth_eq]
  rw [exec_ldr_x ho' (by simpa only [hn, ite_false] using h8)]
  simp (config := {decide := true}) only [runStep_some, runBlock_nil, State.write, Size.bits,
    BitVec.setWidth_eq, hn, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

set_option simprocs false in
/-- `hi += xi`. -/
theorem addLimbs_ok (s : State) :
    WP isa (.block addLimbs) s fun s' =>
      v s' .x4 = (v s .x4 + v s .x9) % 2 ^ 64 ∧ v s' .x5 = (v s .x5 + v s .x10) % 2 ^ 64 ∧
      v s' .x6 = (v s .x6 + v s .x11) % 2 ^ 64 ∧ v s' .x7 = (v s .x7 + v s .x12) % 2 ^ 64 ∧
      v s' .x8 = (v s .x8 + v s .x13) % 2 ^ 64 ∧ Keeps [.x4, .x5, .x6, .x7, .x8] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLimbs, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    v, State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨add_toNat _ _, add_toNat _ _, add_toNat _ _, add_toNat _ _, add_toNat _ _, fun r hr => ?_,
    rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]

set_option simprocs false in
/-- `h += 2¹²⁸`. -/
theorem padBit_ok (s : State) :
    WP isa (.block padBit) s fun s' =>
      v s' .x8 = (v s .x8 + 2 ^ 24) % 2 ^ 64 ∧ Keeps [.x8, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [padBit, runBlock_cons, runStep_some, runBlock_nil,
    exec, v, State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [add_toNat]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

theorem ofNat_toNat5 : (BitVec.ofNat 64 5).toNat = 5 := rfl
theorem ofNat_toNat1 : (BitVec.ofNat 64 1).toNat = 1 := rfl

theorem sub_toNat (a b : BitVec 64) : (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 :=
  BitVec.toNat_sub a b

/-- Normalized limbs of `h mod p`. -/
def Norm (V a0 a1 a2 a3 a4 : Nat) : Prop :=
  val5 a0 a1 a2 a3 a4 = V % Spec.Poly1305.P ∧
    a0 < 2 ^ 26 ∧ a1 < 2 ^ 26 ∧ a2 < 2 ^ 26 ∧ a3 < 2 ^ 26 ∧ a4 < 2 ^ 26

set_option simprocs false in
/-- `normalize` and `plus5`: the mask in `x14` is zero if the limbs of `h mod p` are
`x9`–`x13`, all ones if they are `x4`–`x8`. -/
theorem reduceA_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block (normalize ++ plus5)) s fun s' =>
      (v s .x4 < 2 ^ 26 → v s .x5 < 2 ^ 27 → v s .x6 < 2 ^ 26 → v s .x7 < 2 ^ 26 → v s .x8 < 2 ^ 26 →
        (v s' .x14 = 0 ∧
          Norm (val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8))
            (v s' .x9) (v s' .x10) (v s' .x11) (v s' .x12) (v s' .x13)) ∨
        (v s' .x14 = 2 ^ 64 - 1 ∧
          Norm (val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8))
            (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8))) ∧
      Keeps [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [normalize, plus5, carryStep, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_add, exec_addImm_x (show 5 < 4096 by decide),
    exec_subImm_x (show 1 < 4096 by decide), v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat, sub_toNat, ofNat_toNat5, ofNat_toNat1]
    rcases reduce_arith b0 b1 b2 b3 b4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl with ⟨hb, e, g⟩ | ⟨hb, e, g⟩
    · left
      rw [hb]
      exact ⟨rfl, e, g⟩
    · right
      rw [hb]
      exact ⟨rfl, e, g⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2]

set_option simprocs false in
/-- Selecting `x9`–`x13` over `x4`–`x8` where the mask `x14` is set. -/
theorem select_ok (s : State) :
    WP isa (.block select) s fun s' =>
      s'.gpr .x4 = s.gpr .x9 ^^^ ((s.gpr .x4 ^^^ s.gpr .x9) &&& s.gpr .x14) ∧
      s'.gpr .x5 = s.gpr .x10 ^^^ ((s.gpr .x5 ^^^ s.gpr .x10) &&& s.gpr .x14) ∧
      s'.gpr .x6 = s.gpr .x11 ^^^ ((s.gpr .x6 ^^^ s.gpr .x11) &&& s.gpr .x14) ∧
      s'.gpr .x7 = s.gpr .x12 ^^^ ((s.gpr .x7 ^^^ s.gpr .x12) &&& s.gpr .x14) ∧
      s'.gpr .x8 = s.gpr .x13 ^^^ ((s.gpr .x8 ^^^ s.gpr .x13) &&& s.gpr .x14) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [select, selectLimb, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

theorem select_zero (h g : BitVec 64) : g ^^^ ((h ^^^ g) &&& 0) = g := by simp
theorem select_ones (h g : BitVec 64) : g ^^^ ((h ^^^ g) &&& BitVec.allOnes 64) = h := by
  rw [BitVec.and_allOnes, BitVec.xor_comm h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem eq_zero_of_toNat {a : BitVec 64} (h : a.toNat = 0) : a = 0 := BitVec.eq_of_toNat_eq h
theorem eq_ones_of_toNat {a : BitVec 64} (h : a.toNat = 2 ^ 64 - 1) : a = BitVec.allOnes 64 :=
  BitVec.eq_of_toNat_eq (by rw [h]; rfl)

set_option simprocs false in
/-- The limbs `x4`–`x8` packed into the words `x14, x15, x16`. -/
theorem pack_ok (s : State) :
    WP isa (.block pack) s fun s' =>
      (v s .x4 < 2 ^ 26 → v s .x5 < 2 ^ 26 → v s .x6 < 2 ^ 26 → v s .x7 < 2 ^ 26 →
        v s' .x14 = val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) % 2 ^ 64 ∧
        v s' .x15 = val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) / 2 ^ 64 % 2 ^ 64 ∧
        v s' .x16 = val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) / 2 ^ 128) ∧
      Keeps [.x9, .x14, .x15, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [pack, runBlock_cons, runStep_some, runBlock_nil,
    exec_lsl_x (show 26 < 64 by decide), exec_lsl_x (show 52 < 64 by decide),
    exec_lsl_x (show 14 < 64 by decide), exec_lsl_x (show 40 < 64 by decide),
    exec_lsr_x (show 12 < 64 by decide), exec_lsr_x (show 24 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [lsr_toNat, add_toNat, lsl_toNat]
    exact pack_arith b0 b1 b2 b3
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

set_option simprocs false in
/-- `hi += xi`, with the carries propagated up to `h4`. -/
theorem addCarry_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block (addLimbs ++ carryStep .x4 .x4 .x5 ++ normalize)) s fun s' =>
      (v s .x4 < 2 ^ 27 → v s .x5 < 2 ^ 27 → v s .x6 < 2 ^ 27 → v s .x7 < 2 ^ 27 → v s .x8 < 2 ^ 27 →
        v s .x9 < 2 ^ 27 → v s .x10 < 2 ^ 27 → v s .x11 < 2 ^ 27 → v s .x12 < 2 ^ 27 →
        v s .x13 < 2 ^ 27 →
        val5 (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8) =
          val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) +
            val5 (v s .x9) (v s .x10) (v s .x11) (v s .x12) (v s .x13) ∧
        v s' .x4 < 2 ^ 26 ∧ v s' .x5 < 2 ^ 26 ∧ v s' .x6 < 2 ^ 26 ∧ v s' .x7 < 2 ^ 26 ∧
        v s' .x8 < 2 ^ 29) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLimbs, normalize, carryStep, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat]
    obtain ⟨e, g⟩ := addCarry_arith b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    exact ⟨e, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
      Nat.mod_lt _ (by norm_num), g⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

end VG.Proof.Poly1305.AArch64

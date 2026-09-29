import VerifiedGarbage.Proof.Poly1305.X86.Absorb
import Mathlib.Tactic.Set

/-!
# Poly1305 on x86 (32-bit): the final reduction

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

/-! ## `g = h + 5` -/

section
variable (f : Nat → Nat)
/-- The sums of `h + 5`, with the carries. -/
def gsum : Nat → Nat
  | 0 => f 0 + 5
  | k + 1 => f (k + 1) + gsum k / 2 ^ 32
end

theorem gsum_lt {f : Nat → Nat} (hf : ∀ k < 5, f k < 2 ^ 32) : ∀ k < 5, gsum f k < 2 ^ 33 := by
  intro k hk
  induction k with
  | zero => have := hf 0 (by omega); simp only [gsum]; omega
  | succ k ih => have := ih (by omega); have := hf (k + 1) hk; simp only [gsum]; omega

theorem plus5_eq : plus5 =
    ([.mov .eax (.mem (at_ .edi (hOff 0))), .alu .add .eax (.imm 5), .store (at_ .edi (tOff 0)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (hOff 1))), .alu .adc .eax (.imm 0), .store (at_ .edi (tOff 1)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (hOff 2))), .alu .adc .eax (.imm 0), .store (at_ .edi (tOff 2)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (hOff 3))), .alu .adc .eax (.imm 0), .store (at_ .edi (tOff 3)) .eax] : List Instr) ++
    ([.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm 0), .mov .edx (.reg .eax),
      .shift .shr .eax 2, .mov .ebp (.imm 0), .alu .sub .ebp (.reg .eax)] : List Instr)))) := rfl

section
variable (st : BitVec 32) (s : State) (f : Nat → Nat)
/-- After the words of `g` below `i`. -/
def GInv (i : Nat) (s' : State) : Prop :=
  After st s s' (fun k => if 25 ≤ k ∧ k < 25 + i then gsum f (k - 25) % 2 ^ 32 else f k) [.eax] ∧
    s'.cf = some (decide (2 ^ 32 ≤ gsum f (i - 1)))
end

theorem plus5Step_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat}
    (hw : Words s.mem st f) {i : Nat} (hi : 1 ≤ i ∧ i < 4) {s' : State} (h : GInv st s f i s') :
    WP isa (.block [.mov .eax (.mem (at_ .edi (hOff i))), .alu .adc .eax (.imm 0),
      .store (at_ .edi (tOff i)) .eax]) s' (GInv st s f (i + 1)) := by
  obtain ⟨A, c⟩ := h
  have hlt := gsum_lt (f := f) (fun k hk => hw.lt (by omega))
  refine WP.mono (los_ok (A.ctx hc) A.words (j := i) (j' := 25 + i) rfl (by simp only [tOff]; omega)
    (by omega) (by omega) (.inr ⟨rfl, c⟩) (src_imm 0)) fun s₁ ⟨A₁, c₁⟩ =>
      ⟨(A.trans A₁).mono.congr fun k _ => ?_, ?_⟩
  · simp only [upd]
    rw [ite_eq_right (show ¬ (25 ≤ i ∧ i < 25 + i) by omega),
      show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, carry_dec (hlt (i - 1) (by omega))]
    by_cases e : k = 25 + i
    · subst e
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [gsum, show 25 + (j + 1) - 25 = j + 1 by omega, Nat.add_sub_cancel]
    · rw [ite_eq_right e]
      by_cases e' : 25 ≤ k ∧ k < 25 + i
      · rw [ite_eq_left e', ite_eq_left ⟨e'.1, by omega⟩]
      · rw [ite_eq_right e', ite_eq_right (by omega)]
  · rw [c₁]
    simp only [show i + 1 - 1 = i by omega, show ¬ (25 ≤ i ∧ i < 25 + i) by omega, ite_false]
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, carry_dec (hlt (i - 1) (by omega))]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [gsum, Nat.add_sub_cancel]
    rfl

/-- `g = h + 5`: its low words stored, its top word `g4` in `edx`, and the
mask `-⌊g4 / 4⌋` in `ebp`. -/
theorem plus5_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat}
    (hw : Words s.mem st f) :
    WP isa (.block plus5) s fun s' =>
      After st s s' (fun k => if 25 ≤ k ∧ k < 29 then gsum f (k - 25) % 2 ^ 32 else f k)
        [.eax, .edx, .ebp] ∧
      v s' .edx = (f 4 + gsum f 3 / 2 ^ 32) % 2 ^ 32 ∧
      s'.gpr .ebp = 0 - (s'.gpr .edx >>> 2) := by
  have hlt := gsum_lt (f := f) (fun k hk => hw.lt (by omega))
  rw [plus5_eq]
  refine WP.block_append (WP.mono (los_ok hc hw (j := 0) (j' := 25) rfl rfl (by omega) (by omega)
    (.inl ⟨rfl, rfl⟩) (src_imm 5)) fun s₁ ⟨A₁, c₁⟩ => ?_)
  have h₁ : GInv st s f 1 s₁ := ⟨A₁.congr fun k _ => ?_, by rw [c₁]; rfl⟩
  rotate_left
  · simp only [upd]
    by_cases e : k = 25
    · subst e; simp [gsum]
    · rw [ite_eq_right e, ite_eq_right (by omega)]
  refine WP.block_append (WP.mono (plus5Step_ok hc hw (i := 1) (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (plus5Step_ok hc hw (i := 2) (by omega) h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (plus5Step_ok hc hw (i := 3) (by omega) h₃) fun s₄ ⟨A, c⟩ => ?_)
  have c₄ := A.ctx hc
  refine wp_movm (a := addr st (4 * 4)) (by rw [ea_at, c₄.edi]; rfl) (c₄.inRW (by omega) (by omega))
    fun s₅ u₅ cf₅ => ?_
  refine wp_adcx (readSrc_imm _ _) (by rw [cf₅]; exact c) fun s₆ u₆ _ => ?_
  refine wp_mov fun s₇ u₇ _ => wp_shr (by omega) fun s₈ u₈ => wp_movi fun s₉ u₉ _ => ?_
  refine wp_subx (readSrc_reg _ _) fun s₁₀ u₁₀ _ => WP.block_nil ⟨⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact A.words
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact A.frame
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₀.other r hr.2.2, u₉.other r hr.2.2, u₈.other r hr.1, u₇.other r hr.2.1,
      u₆.other r hr.1, u₅.other r hr.1, A.gpr r (by simp [hr.1])]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, A.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, A.wr]
  · simp only [v]
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr,
      add3_toNat, u₅.gpr, A.words.readW (k := 4) (by omega), show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero,
      carry_dec (hlt 3 (by omega))]
    simp
  · rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₇.other .eax (by decide)]
    rfl

/-! ## The selection -/

theorem select_false (x y : BitVec 32) : x ^^^ ((y ^^^ x) &&& 0) = x := by simp
theorem select_true (x y : BitVec 32) : x ^^^ ((y ^^^ x) &&& BitVec.allOnes 32) = y := by
  rw [BitVec.and_allOnes, BitVec.xor_comm y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The mask for `b`. -/
def maskOf (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

theorem select_mask (x y : BitVec 32) (b : Bool) :
    (x ^^^ ((y ^^^ x) &&& maskOf b)).toNat = if b then y.toNat else x.toNat := by
  cases b
  · simp only [maskOf, Bool.false_eq_true, ite_false, select_false]
  · simp only [maskOf, ite_true, select_true]

/-- Word `k` of `h` replaced by that of `g` if `b`. -/
theorem selectWord_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat}
    (hw : Words s.mem st f) {k : Nat} (hk : k < 4) {b : Bool} (hm : s.gpr .ebp = maskOf b) :
    WP isa (.block (selectWord k)) s fun s' =>
      After st s s' (upd f k (if b then f (25 + k) else f k)) [.eax, .ecx] := by
  have hfit := hc.fit
  refine wp_movm (a := addr st (4 * k)) (by rw [ea_at, hc.edi]; rfl) (hc.inRW (by omega) (by omega))
    fun s₁ u₁ _ => ?_
  have ht : tOff k = 4 * (25 + k) := by simp only [tOff]; omega
  refine wp_movm (a := addr st (4 * (25 + k))) (by rw [ea_at, u₁.other .edi (by decide), hc.edi, ht])
    (by rw [u₁.rd, u₁.wr]; exact hc.inRW (by omega) (by omega)) fun s₂ u₂ _ => ?_
  refine wp_xorx (readSrc_reg _ _) fun s₃ u₃ => wp_andx (readSrc_reg _ _) fun s₄ u₄ => ?_
  refine wp_xorx (readSrc_reg _ _) fun s₅ u₅ => ?_
  have edi₅ : s₅.gpr .edi = st := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.edi]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_store (a := addr st (4 * k)) (by rw [ea_at, edi₅]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₆.mem, mem₅]
    refine (hw.write hfit (by omega) _).congr fun j _ => ?_
    simp only [upd]
    split
    · rw [u₅.gpr, u₄.other .eax (by decide), u₄.gpr, u₃.other .eax (by decide),
        u₃.other .ebp (by decide), u₃.gpr, u₂.gpr, u₂.other .eax (by decide), u₂.other .ebp (by decide),
        u₁.gpr, u₁.other .ebp (by decide), hm, u₁.mem, select_mask, hw.readW (k := k) (by omega),
        hw.readW (k := 25 + k) (by omega)]
    · rfl
  · rw [u₆.mem, mem₅]; exact frame_write (Frame.refl _ _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.gpr, u₅.other r hr.1, u₄.other r hr.2, u₃.other r hr.2, u₂.other r hr.2, u₁.other r hr.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]


/-- The low words selected, from the words `f` (`h` and, at `25 + k`, `g`). -/
def selWords (f : Nat → Nat) (b : Bool) (n : Nat) : Nat → Nat :=
  fun k => if k < n then (if b then f (25 + k) else f k) else f k

theorem selects_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat}
    (hw : Words s.mem st f) {b : Bool} (hm : s.gpr .ebp = maskOf b) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap selectWord)) s fun s' =>
      After st s s' (selWords f b n) [.eax, .ecx] := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨hw.congr fun k _ => by simp [selWords], Frame.refl _ _,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ A₁ => ?_)
    refine WP.mono (selectWord_ok (A₁.ctx hc) A₁.words (k := n) (by omega)
      (by rw [A₁.gpr _ (by decide)]; exact hm)) fun s₂ A₂ => (A₁.trans A₂).mono.congr fun k _ => ?_
    by_cases e : k = n
    · subst e
      simp only [upd, selWords, ite_true, show ¬ 25 + k < k by omega, show ¬ k < k by omega,
        ite_false, show k < k + 1 by omega]
    · simp only [upd, selWords, e, ite_false]
      by_cases e' : k < n
      · simp only [e', ite_true, show k < n + 1 by omega]
      · simp only [e', ite_false, show ¬ k < n + 1 by omega]

/-- The top word: that of `g` (in `edx`) or of `h`, modulo 4. -/
theorem selectTop_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat}
    (hw : Words s.mem st f) {b : Bool} (hm : s.gpr .ebp = maskOf b) :
    WP isa (.block selectTop) s fun s' =>
      After st s s' (upd f 4 ((if b then v s .edx else f 4) % 4)) [.eax, .edx] := by
  have hfit := hc.fit
  refine wp_movm (a := addr st (4 * 4)) (by rw [ea_at, hc.edi]; rfl) (hc.inRW (by omega) (by omega))
    fun s₁ u₁ _ => ?_
  refine wp_xorx (readSrc_reg _ _) fun s₂ u₂ => wp_andx (readSrc_reg _ _) fun s₃ u₃ => ?_
  refine wp_xorx (readSrc_reg _ _) fun s₄ u₄ => wp_andx (readSrc_imm _ _) fun s₅ u₅ => ?_
  have edi₅ : s₅.gpr .edi = st := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.edi]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_store (a := addr st (4 * 4)) (by rw [ea_at, edi₅]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₆.mem, mem₅]
    refine (hw.write hfit (by omega) _).congr fun j _ => ?_
    simp only [upd]
    split
    · rw [u₅.gpr, and3_toNat, u₄.gpr, u₃.other .eax (by decide), u₃.gpr, u₂.other .eax (by decide),
        u₂.other .ebp (by decide), u₂.gpr, u₁.gpr, u₁.other .edx (by decide), u₁.other .ebp (by decide),
        hm, select_mask, hw.readW (k := 4) (by omega)]
    · rfl
  · rw [u₆.mem, mem₅]; exact frame_write (Frame.refl _ _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.gpr, u₅.other r hr.1, u₄.other r hr.1, u₃.other r hr.2, u₂.other r hr.2, u₁.other r hr.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem reduce_eq : reduce = plus5 ++ ((List.range 4).flatMap selectWord ++ selectTop) := by
  simp only [reduce, List.append_assoc]

theorem mask_of {g4 : Nat} (hg : g4 ≤ 5) (x : BitVec 32) (hx : x.toNat = g4) :
    (0 : BitVec 32) - (x >>> 2) = maskOf (decide (g4 / 4 = 1)) := by
  have hs : (x >>> 2).toNat = g4 / 4 := by rw [shr2_toNat, hx]
  rcases (by omega : g4 / 4 = 1 ∨ g4 / 4 = 0) with h | h
  · rw [h] at hs
    rw [show x >>> 2 = 1 from BitVec.eq_of_toNat_eq hs, h]; rfl
  · rw [h] at hs
    rw [show x >>> 2 = 0 from BitVec.eq_of_toNat_eq hs, h]; rfl

/-- `h` reduced fully, in place: its words are those of `h mod p`, the top one less than 4. -/
theorem reduce_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat}
    (hw : Words s.mem st f) (h4 : f 4 ≤ 4) :
    WP isa (.block reduce) s fun s' => ∃ g, After st s s' g [.eax, .ecx, .edx, .ebp] ∧
      (∀ k, 5 ≤ k → k < 25 → g k = f k) ∧ (∀ k, 29 ≤ k → g k = f k) ∧
      hw5 g = hw5 f % P ∧ g 4 < 4 := by
  have hf : ∀ k < 32, f k < 2 ^ 32 := fun k hk => hw.lt hk
  rw [reduce_eq]
  refine WP.block_append (WP.mono (plus5_ok hc hw) fun s₁ ⟨A₁, e₁, m₁⟩ => ?_)
  -- The mask.
  set G : Nat → Nat := fun k => if 25 ≤ k ∧ k < 29 then gsum f (k - 25) % 2 ^ 32 else f k with hG
  set g4 := (f 4 + gsum f 3 / 2 ^ 32) % 2 ^ 32
  have hlt := gsum_lt (f := f) (fun k hk => hf k (by omega))
  have hg4 : g4 ≤ 5 := by
    have := hlt 3 (by omega); have := hf 4 (by omega); simp only [g4]; omega
  have m₁' := m₁.trans (mask_of hg4 _ e₁)
  set b := decide (g4 / 4 = 1) with hb
  refine WP.block_append (WP.mono (selects_ok (A₁.ctx hc) A₁.words m₁' 4 (Nat.le_refl _)) fun s₂ A₂ => ?_)
  refine WP.mono (selectTop_ok ((A₁.trans A₂).ctx hc) A₂.words (by rw [A₂.gpr _ (by decide)]; exact m₁'))
    fun s₃ A₃ => ⟨_, ((A₁.trans A₂).trans A₃).mono, fun k h₁ h₂ => ?_, fun k h₁ => ?_, ?_, ?_⟩
  · simp only [upd, selWords, hG]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [upd, selWords, hG]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · have ed : v s₂ .edx = g4 := by simp only [v]; rw [A₂.gpr _ (by decide)]; exact e₁
    simp only [hw5, upd, selWords, hG, ed, ite_true,
      show (0 : Nat) ≠ 4 by decide, show (1 : Nat) ≠ 4 by decide, show (2 : Nat) ≠ 4 by decide,
      show (3 : Nat) ≠ 4 by decide, ite_false, show (0 : Nat) < 4 by decide,
      show (1 : Nat) < 4 by decide, show (2 : Nat) < 4 by decide, show (3 : Nat) < 4 by decide,
      show ¬ (4 : Nat) < 4 by decide]
    rcases reduce_arith (h0 := f 0) (h1 := f 1) (h2 := f 2) (h3 := f 3) (h4 := f 4)
      (g0 := gsum f 0 % 2 ^ 32) (g1 := gsum f 1 % 2 ^ 32) (g2 := gsum f 2 % 2 ^ 32)
      (g3 := gsum f 3 % 2 ^ 32) (g4 := g4) (hf 0 (by omega)) (hf 1 (by omega)) (hf 2 (by omega))
      (hf 3 (by omega)) h4 rfl rfl rfl rfl rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hbt : b = true := by rw [hb, h1]; rfl
      simp (config := {decide := true}) only [hbt, ite_true, Nat.reduceAdd, Nat.reduceSub]
      exact h2
    · have hbt : b = false := by rw [hb, h1]; rfl
      simp (config := {decide := true}) only [hbt, Bool.false_eq_true, ite_false, Nat.reduceAdd,
        Nat.reduceSub]
      exact h2
  · simp only [upd, ite_true]; exact Nat.mod_lt _ (by omega)

end VG.Proof.Poly1305.X86

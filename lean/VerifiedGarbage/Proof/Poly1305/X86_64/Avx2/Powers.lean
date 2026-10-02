import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load
import VerifiedGarbage.Proof.Poly1305.Horner

/-!
# Poly1305 on x86-64 with AVX2: the powers of `r`

`powers` leaves `r⁴` in the low doubleword of every quadword of `Y` and
`r^(4-k)` in the high doubleword of lane `k`, each as limbs below `2²⁷`.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Spec.Poly1305 (P)

/-- The high doublewords of `Y`. -/
def yh (s : State) (k i : Nat) : Nat := (qw s (yreg i) k).toNat / 2 ^ 32

theorem or_lo {x y : Nat} (hy : y < 2 ^ 32) : (x * 2 ^ 32 ||| y) = x * 2 ^ 32 + y := by
  rw [Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hy]

theorem pick2_toNat (a b : BitVec 64) (l h : Bool) :
    (pick2 a b l h).toNat = (if h then b.toNat / 2 ^ 32 else a.toNat / 2 ^ 32) * 2 ^ 32 +
      (if l then b.toNat % 2 ^ 32 else a.toNat % 2 ^ 32) := by
  have ha := a.isLt
  have hb := b.isLt
  cases l <;> cases h <;>
    simp only [pick2, BitVec.toNat_append, BitVec.extractLsb'_toNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, Bool.false_eq_true, ite_false, ite_true, Nat.pow_zero, Nat.div_one] <;>
    rw [or_lo (Nat.mod_lt _ (by decide))] <;> omega

/-- What `blendY sel lo` writes into `Y_i`: `H_i << 32`, or with `lo`
`H_i << 32 | H_i`. -/
def blT (lo : Bool) (i : Nat) : Q :=
  if lo then .or (.shl (.reg (xi (hreg i))) 32) (.reg (xi (hreg i))) else .shl (.reg (xi (hreg i))) 32

/-- The terms `blendY sel lo` computes. -/
structure BlendShape (σ : Sym) (sel : Nat) (lo : Bool) : Prop where
  y : ∀ i < 5, σ.reg (xi (yreg i)) = .blend (.reg (xi (yreg i))) (blT lo i) sel
  h : ∀ i < 5, σ.reg (xi (hreg i)) = .reg (xi (hreg i))

theorem blT_toNat {s : State} {lo : Bool} {i k : Nat} (hh : hv s k i < 2 ^ 32) :
    ((blT lo i).eval s k).toNat = hv s k i * 2 ^ 32 + (if lo then hv s k i else 0) := by
  rw [natw_ok]
  simp only [hv] at hh ⊢
  cases lo <;> simp only [blT, Bool.false_eq_true, ite_false, ite_true, Q.natw, envOf_v]
  · omega
  · rw [show (qw s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qw s (hreg i) k).toNat * 2 ^ 32 by omega,
      or_lo hh]

/-- `blendY`: the doublewords of `Y` that `sel` selects replaced. -/
theorem blend_ok {σ : Sym} {sel : Nat} {lo : Bool} (hσ : BlendShape σ sel lo) {s s' : State}
    (h : SRel σ s s') {k : Nat} (hk : k < 4) {i : Nat} (hi : i < 5) (hh : hv s k i < 2 ^ 32) :
    hv s' k i = hv s k i ∧
      yl s' k i = (if sel.testBit (2 * k) then (if lo then hv s k i else 0) else yl s k i) ∧
      yh s' k i = (if sel.testBit (2 * k + 1) then hv s k i else yh s k i) := by
  have ey : qw s' (yreg i) k = pick2 (qw s (yreg i) k) ((blT lo i).eval s k) (sel.testBit (2 * k))
      (sel.testBit (2 * k + 1)) := by
    rw [h.reg _ k hk, hσ.y i hi]; simp only [Q.eval, xr_xi]
  have hT := blT_toNat (lo := lo) hh
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, hσ.h i hi]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [ey, pick2_toNat, hT]
    have := (qw s (yreg i) k).isLt
    cases sel.testBit (2 * k) <;> cases sel.testBit (2 * k + 1) <;> cases lo <;>
      simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega
  · simp only [yh]; rw [ey, pick2_toNat, hT]
    have := (qw s (yreg i) k).isLt
    cases sel.testBit (2 * k) <;> cases sel.testBit (2 * k + 1) <;> cases lo <;>
      simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega

/-- Limb functions that agree below 5 and repeat limb 4 above it are equal. -/
theorem ext5 {f g : Nat → Nat} (hf : ∀ j, 4 ≤ j → f j = f 4) (hg : ∀ j, 4 ≤ j → g j = g 4)
    (h : ∀ i < 5, f i = g i) : f = g := by
  funext j
  by_cases hj : j < 5
  · exact h j hj
  · rw [hf j (by omega), hg j (by omega)]; exact h 4 (by decide)

theorem yh_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : yh s k j = yh s k 4 := by
  simp only [yh, yreg_ge h]

theorem mul_ge (a b : Nat → Nat) {j : Nat} (h : 4 ≤ j) : Limbs26.mul a b j = Limbs26.mul a b 4 := by
  match j, h with
  | _ + 4, _ => rfl

/-! ## `initY` -/

def initS : Sym := (Sym.init.run false initY).get (by decide +kernel)
theorem initS_eq : Sym.init.run false initY = some initS := (Option.some_get _).symm
theorem initS_shape : ∀ i < 5, initS.reg (xi (yreg i)) =
      .or (.reg (xi (hreg i))) (.shl (.reg (xi (hreg i))) 32) ∧
    initS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem initY_ok {s : State} (hh : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 32) :
    WP isa (.block initY) s fun s' => vec s s' = s' ∧ ∀ k < 4, ∀ i < 5,
      hv s' k i = hv s k i ∧ yl s' k i = hv s k i ∧ yh s' k i = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) initS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qw s' (yreg i) k).toNat = hv s k i * 2 ^ 32 + hv s k i := by
    rw [h.natw _ hk, (initS_shape i hi).1]
    have := hh k hk i hi
    simp only [Q.natw, envOf_v, hv] at this ⊢
    rw [show (qw s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qw s (hreg i) k).toNat * 2 ^ 32 by omega,
      Nat.or_comm, or_lo this]
  have := hh k hk i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, (initS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [e]; omega
  · simp only [yh]; rw [e]; omega

/-! ## `blendY` -/

def bl1 : Sym := (Sym.init.run false (blendY 0x2A false)).get (by decide +kernel)
def bl2 : Sym := (Sym.init.run false (blendY 0x0A false)).get (by decide +kernel)
def bl3 : Sym := (Sym.init.run false (blendY 0x57 true)).get (by decide +kernel)
theorem bl1_eq : Sym.init.run false (blendY 0x2A false) = some bl1 := (Option.some_get _).symm
theorem bl2_eq : Sym.init.run false (blendY 0x0A false) = some bl2 := (Option.some_get _).symm
theorem bl3_eq : Sym.init.run false (blendY 0x57 true) = some bl3 := (Option.some_get _).symm

theorem bl1_shape : BlendShape bl1 0x2A false :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem bl2_shape : BlendShape bl2 0x0A false :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem bl3_shape : BlendShape bl3 0x57 true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## `r` into `H` -/

def loadRg : List Instr := [
  .movImm64 .rax 0x0ffffffc0fffffff, .mov .r10 (.mem (at_ .rdi 24)), .alu .and .r10 (.reg .rax),
  .movImm64 .rax 0x0ffffffc0ffffffc, .mov .r11 (.mem (at_ .rdi 32)), .alu .and .r11 (.reg .rax)]
def loadRv : List Instr :=
  bcast (dreg 0) .r10 ++ bcast (dreg 1) .r11 ++ split ++
  (List.range 5).map fun i => .vop (.vmovdqa .l256 (hreg i) (dreg i))
theorem loadR_eq : loadR = loadRg ++ loadRv := rfl

def lrS : Sym := (Sym.init.run false loadRv).get (by decide +kernel)
theorem lrS_eq : Sym.init.run false loadRv = some lrS := (Option.some_get _).symm

section
variable (E : Env) (k : Nat)
theorem lrS_0 : (lrS.reg (xi (hreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_1 : (lrS.reg (xi (hreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_2 : (lrS.reg (xi (hreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_3 : (lrS.reg (xi (hreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_4 : (lrS.reg (xi (hreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

/-- `r` as a number, from `r10` and `r11`. -/
def rN (s : State) : Nat := (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat

theorem loadRv_ok (s : State) :
    WP isa (.block loadRv) s fun s' => vec s s' = s' ∧ (∀ k < 4, ∀ i < 5, hv s' k i = hv s' 0 i) ∧
      Limbs26.val (hv s' 0) = rN s ∧ ∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 26 := by
  refine WP.mono (run_ok (by intro h; cases h) lrS_eq) fun s' h => ?_
  have e : ∀ k < 4, hv s' k 0 = (s.gpr .r10).toNat * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = (s.gpr .r10).toNat * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = (s.gpr .r11).toNat * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| (s.gpr .r10).toNat / 2 ^ 52 ∧
      hv s' k 3 = (s.gpr .r11).toNat * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = (s.gpr .r11).toNat / 2 ^ 40 := fun k hk =>
    ⟨by rw [hv, h.natw _ hk, lrS_0]; rfl, by rw [hv, h.natw _ hk, lrS_1]; rfl,
      by rw [hv, h.natw _ hk, lrS_2]; rfl, by rw [hv, h.natw _ hk, lrS_3]; rfl,
      by rw [hv, h.natw _ hk, lrS_4]; rfl⟩
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  have e₀ := e 0 (by decide)
  refine ⟨h.eq, fun k hk i hi => ?_, ?_, fun k hk i hi => ?_⟩
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [a0, e₀.1]
    · rw [a1, e₀.2.1]
    · rw [a2, e₀.2.2.1]
    · rw [a3, e₀.2.2.2.1]
    · rw [a4, e₀.2.2.2.2]
  · rw [Limbs26.val, e₀.1, e₀.2.1, e₀.2.2.1, e₀.2.2.2.1, e₀.2.2.2.2, rN]
    exact Limbs26.split_val l _
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    rw [Limbs26.split_or l] at a2
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [a0]; omega
    · rw [a1]; omega
    · rw [a2]; omega
    · rw [a3]; omega
    · rw [a4]; omega

/-! ## The powers -/

theorem val_congr {f g : Nat → Nat} (h : ∀ i < 5, f i = g i) : Limbs26.val f = Limbs26.val g := by
  simp only [Limbs26.val, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide)]

/-- `mul` of lanes that all hold `A`, times `B`. -/
theorem mul_step {s s' : State} (M : MulPost s s') {A B : Nat → Nat} (hA : ∀ j, 4 ≤ j → A j = A 4)
    (hB : ∀ j, 4 ≤ j → B j = B 4) (hH : ∀ k < 4, ∀ i < 5, hv s k i = A i)
    (hY : ∀ k < 4, ∀ i < 5, yl s k i = B i) :
    ∀ k < 4, ∀ i < 5, hv s' k i = Limbs26.mul A B i ∧ yl s' k i = yl s k i ∧ yh s' k i = yh s k i := by
  intro k hk i hi
  refine ⟨?_, by simp only [yl, M.y i hi k hk], by simp only [yh, M.y i hi k hk]⟩
  rw [M.h k hk i hi, ext5 (f := hv s k) (fun _ h => hv_ge s k h) hA (hH k hk),
    ext5 (f := yl s k) (fun _ h => yl_ge s k h) hB (hY k hk)]

def powersV : List Instr :=
  loadRv ++ (initY ++ (mul ++ (blendY 0x2A false ++ (mul ++ (blendY 0x0A false ++
    (mul ++ blendY 0x57 true))))))

theorem powers_eq : powers = loadRg ++ powersV := by
  simp only [powers, loadR_eq, powersV, List.append_assoc]

/-- What `powers` leaves in `Y`, for `r = R`. -/
structure YInv (s : State) (R : Nat) : Prop where
  lo : ∀ k < 4, Limbs26.val (yl s k) ≡ R ^ 4 [MOD P]
  hi : ∀ k < 4, Limbs26.val (yh s k) ≡ R ^ (4 - k) [MOD P]
  lob : ∀ k < 4, ∀ i < 5, yl s k i < 2 ^ 27
  hib : ∀ k < 4, ∀ i < 5, yh s k i < 2 ^ 27

theorem mul_modEq {a b : Nat → Nat} {x y : Nat} (ha : Limbs26.val a ≡ x [MOD P])
    (hb : Limbs26.val b ≡ y [MOD P]) : Limbs26.val (Limbs26.mul a b) ≡ x * y [MOD P] :=
  (Limbs26.mul_mod a b).trans (ha.mul hb)

theorem powersV_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) :
    WP isa (.block powersV) s fun s' => vec s s' = s' ∧ YInv s' (rN s) := by
  refine WP.block_append (WP.mono (loadRv_ok s) fun s₁ ⟨v₁, U₁, V₁, B₁⟩ => ?_)
  have LL : ∀ j, 4 ≤ j → hv s₁ 0 j = hv s₁ 0 4 := fun j h => hv_ge s₁ 0 h
  refine WP.block_append (WP.mono (initY_ok fun k hk i hi => by have := B₁ k hk i hi; omega)
    fun s₂ ⟨v₂, I₂⟩ => ?_)
  have h₂ : ∀ k < 4, ∀ i < 5, hv s₂ k i = hv s₁ 0 i ∧ yl s₂ k i = hv s₁ 0 i ∧ yh s₂ k i = hv s₁ 0 i := by
    intro k hk i hi; obtain ⟨a, b, c⟩ := I₂ k hk i hi; rw [U₁ k hk i hi] at a b c; exact ⟨a, b, c⟩
  have hb₁ : ∀ i < 5, hv s₁ 0 i < 2 ^ 26 := B₁ 0 (by decide)
  have r8 : ∀ {t : State}, vec s t = t → t.gpr .r8 = 0x3ffffff := fun h => by rw [vec_gpr h, hr8]
  have v₂' := vec_trans v₁ v₂
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₂', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₃ M₃ => ?_)
  · rw [(h₂ k hk i hi).1]; have := hb₁ i hi; omega
  · rw [(h₂ k hk i hi).2.1]; have := hb₁ i hi; omega
  have m₃ := mul_step M₃ LL LL (fun k hk i hi => (h₂ k hk i hi).1) (fun k hk i hi => (h₂ k hk i hi).2.1)
  -- `r²` in `H`; `Y` = `r` in both doublewords.
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) bl1_eq) fun s₄ h₄ => ?_)
  have e₄ : ∀ k < 4, ∀ i < 5, hv s₄ k i = Limbs26.mul (hv s₁ 0) (hv s₁ 0) i ∧ yl s₄ k i = hv s₁ 0 i ∧
      yh s₄ k i = if k < 3 then Limbs26.mul (hv s₁ 0) (hv s₁ 0) i else hv s₁ 0 i := by
    intro k hk i hi
    obtain ⟨a₃, b₃, c₃⟩ := m₃ k hk i hi
    have := M₃.hb k hk i hi
    obtain ⟨a, b, c⟩ := blend_ok bl1_shape h₄ hk hi (by omega)
    rw [a, b, c, a₃, b₃, c₃, (h₂ k hk i hi).2.1, (h₂ k hk i hi).2.2]
    refine ⟨rfl, ?_⟩
    rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) only [ite_true, ite_false]
  have v₄ := vec_trans (vec_trans v₂' M₃.vec) h₄.eq
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₄, fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₅ M₅ => ?_)
  · rw [(e₄ k hk i hi).1, ← (m₃ k hk i hi).1]; have := M₃.hb k hk i hi; omega
  · rw [(e₄ k hk i hi).2.1]; have := hb₁ i hi; omega
  have m₅ := mul_step (A := Limbs26.mul (hv s₁ 0) (hv s₁ 0)) M₅ (fun _ h => mul_ge _ _ h) LL (fun k hk i hi => (e₄ k hk i hi).1)
    (fun k hk i hi => (e₄ k hk i hi).2.1)
  -- `r³` in `H`; `r³` into the high doublewords of lanes 0 and 1.
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) bl2_eq) fun s₆ h₆ => ?_)
  have e₆ : ∀ k < 4, ∀ i < 5,
      hv s₆ k i = Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i ∧ yl s₆ k i = hv s₁ 0 i ∧
      yh s₆ k i = if k < 2 then Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i
        else if k < 3 then Limbs26.mul (hv s₁ 0) (hv s₁ 0) i else hv s₁ 0 i := by
    intro k hk i hi
    obtain ⟨a₅, b₅, c₅⟩ := m₅ k hk i hi
    have := M₅.hb k hk i hi
    obtain ⟨a, b, c⟩ := blend_ok bl2_shape h₆ hk hi (by omega)
    rw [a, b, c, a₅, b₅, c₅, (e₄ k hk i hi).2.1, (e₄ k hk i hi).2.2]
    refine ⟨rfl, ?_⟩
    rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) only [ite_true, ite_false]
  have v₆ := vec_trans (vec_trans v₄ M₅.vec) h₆.eq
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₆, fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₇ M₇ => ?_)
  · rw [(e₆ k hk i hi).1, ← (m₅ k hk i hi).1]; have := M₅.hb k hk i hi; omega
  · rw [(e₆ k hk i hi).2.1]; have := hb₁ i hi; omega
  have m₇ := mul_step (A := Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0)) M₇
    (fun _ h => mul_ge _ _ h) LL (fun k hk i hi => (e₆ k hk i hi).1)
    (fun k hk i hi => (e₆ k hk i hi).2.1)
  -- `r⁴` into the low doublewords, and the high one of lane 0.
  refine WP.mono (run_ok (by intro h; cases h) bl3_eq) fun s₈ h₈ => ?_
  have e₈ : ∀ k < 4, ∀ i < 5,
      yl s₈ k i = hv s₇ 0 i ∧
      yh s₈ k i = if k < 1 then hv s₇ 0 i
        else if k < 2 then Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i
        else if k < 3 then Limbs26.mul (hv s₁ 0) (hv s₁ 0) i else hv s₁ 0 i := by
    intro k hk i hi
    obtain ⟨_, b₇, c₇⟩ := m₇ k hk i hi
    have := M₇.hb k hk i hi
    obtain ⟨_, b, c⟩ := blend_ok bl3_shape h₈ hk hi (by omega)
    rw [b, c, b₇, c₇, (e₆ k hk i hi).2.2, (m₇ k hk i hi).1, (m₇ 0 (by decide) i hi).1]
    rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) only [ite_true, ite_false]
  refine ⟨vec_trans (vec_trans v₆ M₇.vec) h₈.eq, ?_⟩
  -- Values and bounds of the powers.
  have q₁ : Limbs26.val (hv s₁ 0) ≡ rN s [MOD P] := by rw [V₁]
  have q₂ := mul_modEq q₁ q₁
  have q₃ := mul_modEq q₂ q₁
  have q₄ : Limbs26.val (hv s₇ 0) ≡ rN s ^ 4 [MOD P] := by
    rw [val_congr (m₇ 0 (by decide) · · |>.1), show rN s ^ 4 = rN s * rN s * rN s * rN s by ring]
    exact mul_modEq q₃ q₁
  have b₂ : ∀ i < 5, Limbs26.mul (hv s₁ 0) (hv s₁ 0) i < 2 ^ 27 := fun i hi => by
    rw [← (m₃ 0 (by decide) i hi).1]; exact M₃.hb 0 (by decide) i hi
  have b₃ : ∀ i < 5, Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i < 2 ^ 27 := fun i hi => by
    rw [← (m₅ 0 (by decide) i hi).1]; exact M₅.hb 0 (by decide) i hi
  have b₄ : ∀ i < 5, hv s₇ 0 i < 2 ^ 27 := fun i hi => M₇.hb 0 (by decide) i hi
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [val_congr (e₈ k hk · · |>.1)]; exact q₄
  · rcases cases4 hk with rfl | rfl | rfl | rfl
    · rw [val_congr (e₈ 0 (by decide) · · |>.2)]; exact q₄
    · rw [val_congr (g := Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0)) fun i hi => by
        simp (config := { decide := true }) only [(e₈ 1 (by decide) i hi).2, ite_true, ite_false]]
      simpa only [show rN s ^ (4 - 1) = rN s * rN s * rN s by ring] using q₃
    · rw [val_congr (g := Limbs26.mul (hv s₁ 0) (hv s₁ 0)) fun i hi => by
        simp (config := { decide := true }) only [(e₈ 2 (by decide) i hi).2, ite_true, ite_false]]
      simpa only [show rN s ^ (4 - 2) = rN s * rN s by ring] using q₂
    · rw [val_congr (g := hv s₁ 0) fun i hi => by
        simp (config := { decide := true }) only [(e₈ 3 (by decide) i hi).2, ite_false]]
      simpa only [show rN s ^ (4 - 3) = rN s by ring] using q₁
  · rw [(e₈ k hk i hi).1]; exact b₄ i hi
  · rw [(e₈ k hk i hi).2]
    have := hb₁ i hi; have := b₂ i hi; have := b₃ i hi; have := b₄ i hi
    split <;> [omega; split <;> [omega; split <;> omega]]

end VG.Proof.Poly1305.X86_64.Avx2

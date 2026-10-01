import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Load
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Powers

/-!
# Poly1305 on x86-64 with AVX-512: the powers of `r`

Untrusted: everything here is checked by Lean. `powers` leaves `r⁸` in the
low doubleword of every quadword of `Y` and `r^(8 - π k)` in the high
doubleword of quadword `k`, each as limbs below `2²⁷`: `r²`, then `(r⁴, r³)`
in each lane, then `(r^(4 - j), r^(4 - j))` in lane `j` multiplied by
`(r⁴, 1)`.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr or_lo ext5 mul_ge val_congr
  mul_modEq rN hreg_ge yreg_ge)
open VG.Spec.Poly1305 (P)

/-- The high doublewords of `Y`, and the limbs of `D`. -/
def yh (s : State) (k i : Nat) : Nat := (qz s (yreg i) k).toNat / 2 ^ 32
def dv (s : State) (k i : Nat) : Nat := (qz s (dreg i) k).toNat

theorem yh_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : yh s k j = yh s k 4 := by
  simp only [yh, yreg_ge h]

theorem cases5 {i : Nat} (hi : i < 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega

/-- `f` holds the limbs of `r10 + 2⁶⁴ r11` (of `s`), as `split` computes
them. (Stated inline, as in `Limbs26`: a definition whose body divides would
be unfolded by `rfl`, very slowly.) -/
def SplitOf (s : State) (f : Nat → Nat) : Prop :=
  f 0 = (s.gpr .r10).toNat * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
  f 1 = (s.gpr .r10).toNat * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
  f 2 = ((s.gpr .r11).toNat * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| (s.gpr .r10).toNat / 2 ^ 52) ∧
  f 3 = (s.gpr .r11).toNat * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
  f 4 = (s.gpr .r11).toNat / 2 ^ 40

theorem SplitOf.eq {s : State} {f g : Nat → Nat} (hf : SplitOf s f) (hg : SplitOf s g) :
    ∀ i < 5, f i = g i := by
  intro i hi
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  obtain ⟨b0, b1, b2, b3, b4⟩ := hg
  rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

theorem SplitOf.val {s : State} {f : Nat → Nat} (hf : SplitOf s f) : Limbs26.val f = rN s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  rw [Limbs26.val, a0, a1, a2, a3, a4, rN]
  exact Limbs26.split_val (s.gpr .r10).isLt _

theorem SplitOf.lt {s : State} {f : Nat → Nat} (hf : SplitOf s f) : ∀ i < 5, f i < 2 ^ 26 := by
  intro i hi
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  rw [Limbs26.split_or l] at a2
  rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
  · rw [a0]; omega
  · rw [a1]; omega
  · rw [a2]; omega
  · rw [a3]; omega
  · rw [a4]; omega

theorem SplitOf.congr {s s' : State} (hg : s'.gpr = s.gpr) {f : Nat → Nat} (hf : SplitOf s f) :
    SplitOf s' f := by
  simp only [SplitOf, hg]; exact hf

/-! ## `r` into `D` and `H` -/

def lrS : Sym := (Sym.init.run false loadRv).get (by decide +kernel)
theorem lrS_eq : Sym.init.run false loadRv = some lrS := (Option.some_get _).symm

section
variable (E : Env) (k : Nat)
theorem lrS_h0 : (lrS.reg (xi (hreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h1 : (lrS.reg (xi (hreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h2 : (lrS.reg (xi (hreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_h3 : (lrS.reg (xi (hreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h4 : (lrS.reg (xi (hreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
theorem lrS_d0 : (lrS.reg (xi (dreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d1 : (lrS.reg (xi (dreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d2 : (lrS.reg (xi (dreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_d3 : (lrS.reg (xi (dreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d4 : (lrS.reg (xi (dreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

def srS : Sym := (Sym.init.run false splitR).get (by decide +kernel)
theorem srS_eq : Sym.init.run false splitR = some srS := (Option.some_get _).symm
theorem srS_keep : ∀ i < 5, srS.reg (xi (hreg i)) = .reg (xi (hreg i)) ∧
    srS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env) (k : Nat)
theorem srS_d0 : (srS.reg (xi (dreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d1 : (srS.reg (xi (dreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d2 : (srS.reg (xi (dreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem srS_d3 : (srS.reg (xi (dreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d4 : (srS.reg (xi (dreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

theorem loadRv_ok (s : State) :
    WP isa (.block loadRv) s fun s' => vec s s' = s' ∧
      ∀ k < 8, SplitOf s (hv s' k) ∧ SplitOf s (dv s' k) := by
  refine WP.mono (run_ok (by intro h; cases h) lrS_eq) fun s' h => ⟨h.eq, fun k hk => ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hv] <;> rw [h.natw _ hk]
    · rw [lrS_h0]; rfl
    · rw [lrS_h1]; rfl
    · rw [lrS_h2]; rfl
    · rw [lrS_h3]; rfl
    · rw [lrS_h4]; rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [dv] <;> rw [h.natw _ hk]
    · rw [lrS_d0]; rfl
    · rw [lrS_d1]; rfl
    · rw [lrS_d2]; rfl
    · rw [lrS_d3]; rfl
    · rw [lrS_d4]; rfl

theorem splitR_ok (s : State) :
    WP isa (.block splitR) s fun s' => vec s s' = s' ∧
      ∀ k < 8, SplitOf s (dv s' k) ∧ ∀ i < 5, qz s' (hreg i) k = qz s (hreg i) k ∧
        qz s' (yreg i) k = qz s (yreg i) k := by
  refine WP.mono (run_ok (by intro h; cases h) srS_eq) fun s' h => ⟨h.eq, fun k hk => ⟨?_, fun i hi => ⟨?_, ?_⟩⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [dv] <;> rw [h.natw _ hk]
    · rw [srS_d0]; rfl
    · rw [srS_d1]; rfl
    · rw [srS_d2]; rfl
    · rw [srS_d3]; rfl
    · rw [srS_d4]; rfl
  · rw [h.reg _ k hk, (srS_keep i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (srS_keep i hi).2]; simp only [Q.eval, xr_xi]

/-! ## `initY` -/

def initS : Sym := (Sym.init.run false initY).get (by decide +kernel)
theorem initS_eq : Sym.init.run false initY = some initS := (Option.some_get _).symm
theorem initS_shape : ∀ i < 5, initS.reg (xi (yreg i)) =
      .or (.reg (xi (hreg i))) (.shl (.reg (xi (hreg i))) 32) ∧
    initS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem initY_ok {s : State} (hh : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 32) :
    WP isa (.block initY) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = hv s k i ∧ yl s' k i = hv s k i ∧ yh s' k i = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) initS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qz s' (yreg i) k).toNat = hv s k i * 2 ^ 32 + hv s k i := by
    rw [h.natw _ hk, (initS_shape i hi).1]
    have := hh k hk i hi
    simp only [Q.natw, envOf_v, hv] at this ⊢
    rw [show (qz s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qz s (hreg i) k).toNat * 2 ^ 32 by omega,
      Nat.or_comm, or_lo this]
  have := hh k hk i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, (initS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [e]; omega
  · simp only [yh]; rw [e]; omega

/-! ## `pairs` -/

def prS : Sym := (Sym.init.run false pairs).get (by decide +kernel)
theorem prS_eq : Sym.init.run false pairs = some prS := (Option.some_get _).symm
theorem prS_shape : ∀ i < 5, prS.reg (xi (hreg i)) =
      .unpl (.reg (xi (hreg i))) (.shr (.reg (xi (yreg i))) 32) ∧
    prS.reg (xi (yreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem pairs_ok (s : State) :
    WP isa (.block pairs) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = (if k % 2 = 0 then hv s k i else yh s (k - 1) i) ∧
      (qz s' (yreg i) k).toNat = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) prS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv, yh]
    rw [h.natw _ hk, (prS_shape i hi).1]
    simp only [Q.natw, envOf_v]
  · rw [h.natw _ hk, (prS_shape i hi).2]
    simp only [Q.natw, envOf_v, hv]

/-! ## `spread` -/

def spS : Sym := (Sym.init.run false spread).get (by decide +kernel)
theorem spS_eq : Sym.init.run false spread = some spS := (Option.some_get _).symm

/-- Lane `j` of each `H_i` becomes quadword `0` of `H_i` (`j = 0`), quadword
`1` of `H_i`, quadword `0` of `Y_i`, or quadword `0` of `D_i` (`j = 3`). -/
def spH (E : Env) (i k : Nat) : Nat :=
  if k / 2 = 0 then E.v (xi (hreg i)) 0 else if k / 2 = 1 then E.v (xi (hreg i)) 1
  else if k / 2 = 2 then E.v (xi (yreg i)) 0 else E.v (xi (dreg i)) 0

/-- Each `Y_i` becomes `(H_i[0], 1)` in each lane (`1` as limbs, from `rax`). -/
def spY (E : Env) (i k : Nat) : Nat :=
  if k % 2 = 0 then E.v (xi (hreg i)) 0
  else if i = 0 then E.g .rax else (2 ^ 64 - 1 - E.g .rax) &&& E.g .rax

theorem spS_h (E : Env) : ∀ i < 5, ∀ k < 8, (spS.reg (xi (hreg i))).natw E k = spH E i k := by
  intro i hi k hk
  rcases cases5 hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem spS_y (E : Env) : ∀ i < 5, ∀ k < 8, (spS.reg (xi (yreg i))).natw E k = spY E i k := by
  intro i hi k hk
  rcases cases5 hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The limbs of 1. -/
def one (i : Nat) : Nat := if i = 0 then 1 else 0

theorem one_val : Limbs26.val one = 1 := rfl

theorem spread_ok {s : State} (hax : s.gpr .rax = 1) :
    WP isa (.block spread) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = (if k / 2 = 0 then hv s 0 i else if k / 2 = 1 then hv s 1 i
        else if k / 2 = 2 then (qz s (yreg i) 0).toNat else dv s 0 i) ∧
      (qz s' (yreg i) k).toNat = if k % 2 = 0 then hv s 0 i else one i := by
  refine WP.mono (run_ok (by intro h; cases h) spS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv]
    rw [h.natw _ hk, spS_h _ i hi k hk]
    simp only [spH, envOf_v, dv]
  · rw [h.natw _ hk, spS_y _ i hi k hk]
    have ax : (envOf s).g .rax = 1 := by simp only [envOf, hax]; rfl
    simp only [spY, ax, one, envOf_v, hv]
    split
    · rfl
    · split <;> decide

/-! ## `finishY` -/

def fyS : Sym := (Sym.init.run false finishY).get (by decide +kernel)
theorem fyS_eq : Sym.init.run false finishY = some fyS := (Option.some_get _).symm
theorem fyS_shape : ∀ i < 5, fyS.reg (xi (yreg i)) =
      .or (.shl (.reg (xi (hreg i))) 32) (.bc (.reg (xi (hreg i)))) ∧
    fyS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem finishY_ok {s : State} (hh : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 32) :
    WP isa (.block finishY) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      hv s' k i = hv s k i ∧ yl s' k i = hv s 0 i ∧ yh s' k i = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) fyS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qz s' (yreg i) k).toNat = hv s k i * 2 ^ 32 + hv s 0 i := by
    rw [h.natw _ hk, (fyS_shape i hi).1]
    have := hh k hk i hi
    have := hh 0 (by decide) i hi
    simp only [Q.natw, envOf_v, hv] at *
    rw [show (qz s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qz s (hreg i) k).toNat * 2 ^ 32 by omega,
      or_lo (by omega)]
  have := hh k hk i hi
  have := hh 0 (by decide) i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, (fyS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [e]; omega
  · simp only [yh]; rw [e]; omega

/-! ## The powers -/

/-- What `powers` leaves in `Y`, for `r = R`. -/
structure YInv (s : State) (R : Nat) : Prop where
  lo : ∀ k < 8, Limbs26.val (yl s k) ≡ R ^ 8 [MOD P]
  hi : ∀ k < 8, Limbs26.val (yh s k) ≡ R ^ (8 - pi k) [MOD P]
  lob : ∀ k < 8, ∀ i < 5, yl s k i < 2 ^ 27
  hib : ∀ k < 8, ∀ i < 5, yh s k i < 2 ^ 27

def powersV : List Instr :=
  loadRv ++ (initY ++ (mul ++ (pairs ++ (mul ++ (splitR ++ (spread ++ (mul ++ finishY)))))))

theorem powers_eq : powers = loadRg ++ powersV := by
  simp only [powers, powersV, List.append_assoc]

theorem hv_ge' (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : hv s k j = hv s k 4 := hv_ge s k h

/-- Limb functions equal below 5 (and both repeating limb 4) are equal. -/
theorem fext {f g : Nat → Nat} (hf : ∀ j, 4 ≤ j → f j = f 4) (hg : ∀ j, 4 ≤ j → g j = g 4)
    (h : ∀ i < 5, f i = g i) : f = g := ext5 hf hg h

theorem one_ge {j : Nat} (h : 4 ≤ j) : one j = one 4 := by
  simp only [one, show j ≠ 0 by omega, show (4 : Nat) ≠ 0 by decide, ite_false]

theorem one_lt {i : Nat} : one i < 2 ^ 27 := by
  simp only [one]; split <;> decide

/-- Limbs by lane: `a` in lane 0, `b` in lane 1, `c` in lane 2 and `d` in lane 3. -/
def quad (a b c d : Nat → Nat) (k : Nat) : Nat → Nat :=
  if k / 2 = 0 then a else if k / 2 = 1 then b else if k / 2 = 2 then c else d

theorem quad_apply (a b c d : Nat → Nat) (k i : Nat) :
    quad a b c d k i = (if k / 2 = 0 then a i else if k / 2 = 1 then b i else if k / 2 = 2 then c i else d i) := by
  simp only [quad]; split <;> [rfl; split <;> [rfl; split <;> rfl]]

theorem quad_ge {a b c d : Nat → Nat} (ha : ∀ j, 4 ≤ j → a j = a 4) (hb : ∀ j, 4 ≤ j → b j = b 4)
    (hc : ∀ j, 4 ≤ j → c j = c 4) (hd : ∀ j, 4 ≤ j → d j = d 4) (k : Nat) :
    ∀ j, 4 ≤ j → quad a b c d k j = quad a b c d k 4 := fun j h => by
  simp only [quad]; split <;> [exact ha j h; split <;> [exact hb j h; split <;> [exact hc j h; exact hd j h]]]

/-- Limbs by quadword: `a` in the even ones, `b` in the odd ones. -/
def alt (a b : Nat → Nat) (k : Nat) : Nat → Nat := if k % 2 = 0 then a else b

theorem alt_apply (a b : Nat → Nat) (k i : Nat) : alt a b k i = if k % 2 = 0 then a i else b i := by
  simp only [alt]; split <;> rfl

theorem alt_of_even {a b : Nat → Nat} {k : Nat} (h : k % 2 = 0) : alt a b k = a := by
  simp only [alt, h, ite_true]

theorem alt_of_odd {a b : Nat → Nat} {k : Nat} (h : k % 2 = 1) : alt a b k = b := by
  simp only [alt, h, show (1 : Nat) ≠ 0 by decide, ite_false]

theorem alt_ge {a b : Nat → Nat} (ha : ∀ j, 4 ≤ j → a j = a 4) (hb : ∀ j, 4 ≤ j → b j = b 4) (k : Nat) :
    ∀ j, 4 ≤ j → alt a b k j = alt a b k 4 := fun j h => by
  simp only [alt]; split <;> [exact ha j h; exact hb j h]

theorem powersV_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hax : s.gpr .rax = 1) :
    WP isa (.block powersV) s fun s' => vec s s' = s' ∧ YInv s' (rN s) := by
  have r8 : ∀ {t : State}, vec s t = t → t.gpr .r8 = 0x3ffffff := fun h => by rw [vec_gpr h, hr8]
  have ax : ∀ {t : State}, vec s t = t → t.gpr .rax = 1 := fun h => by rw [vec_gpr h, hax]
  -- `r` in `H` and `D`.
  refine WP.block_append (WP.mono (loadRv_ok s) fun s₁ ⟨v₁, L₁⟩ => ?_)
  let rA := hv s₁ 0
  have rS : SplitOf s rA := (L₁ 0 (by decide)).1
  have A_lt := fun {i : Nat} (hi : i < 5) => rS.lt i hi
  have hA₁ : ∀ k < 8, ∀ i < 5, hv s₁ k i = rA i := fun k hk => (L₁ k hk).1.eq rS
  have rA_ge : ∀ j, 4 ≤ j → rA j = rA 4 := fun _ h => hv_ge _ _ h
  -- `Y = r` in both doublewords.
  refine WP.block_append (WP.mono (initY_ok fun k hk i hi => by
    rw [hA₁ k hk i hi]; have := A_lt hi; omega) fun s₂ ⟨v₂, I₂⟩ => ?_)
  have v₂' := vec_trans v₁ v₂
  -- `H = r²`.
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₂', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₃ M₃ => ?_)
  · rw [(I₂ k hk i hi).1, hA₁ k hk i hi]; have := A_lt hi; omega
  · rw [(I₂ k hk i hi).2.1, hA₁ k hk i hi]; have := A_lt hi; omega
  have hA₂ : ∀ k < 8, hv s₂ k = rA := fun k hk =>
    fext (fun _ h => hv_ge _ _ h) rA_ge fun i hi => by rw [(I₂ k hk i hi).1, hA₁ k hk i hi]
  have yA₂ : ∀ k < 8, yl s₂ k = rA := fun k hk =>
    fext (fun _ h => yl_ge _ _ h) rA_ge fun i hi => by rw [(I₂ k hk i hi).2.1, hA₁ k hk i hi]
  let B := Limbs26.mul (rA) (rA)
  have e₃ : ∀ k < 8, ∀ i < 5, hv s₃ k i = B i := fun k hk i hi => by
    rw [M₃.h k hk i hi, hA₂ k hk, yA₂ k hk]
  have yh₃ : ∀ k < 8, ∀ i < 5, yh s₃ k i = rA i := fun k hk i hi => by
    simp only [yh]; rw [M₃.y i hi k hk]
    have := (I₂ k hk i hi).2.2; simp only [yh] at this; rw [this, hA₁ k hk i hi]
  have B_lt : ∀ i < 5, B i < 2 ^ 27 := fun i hi => by rw [← e₃ 0 (by decide) i hi]; exact M₃.hb 0 (by decide) i hi
  -- `H = (r², r)` in each lane, `Y = r²`.
  refine WP.block_append (WP.mono (pairs_ok s₃) fun s₄ ⟨v₄, P₄⟩ => ?_)
  have v₄' := vec_trans (vec_trans v₂' M₃.vec) v₄
  have h₄ : ∀ k < 8, ∀ i < 5, hv s₄ k i = (if k % 2 = 0 then B i else rA i) := fun k hk i hi => by
    rw [(P₄ k hk i hi).1]; split
    · exact e₃ k hk i hi
    · exact yh₃ (k - 1) (by omega) i hi
  have y₄ : ∀ k < 8, ∀ i < 5, yl s₄ k i = B i := fun k hk i hi => by
    simp only [yl]; rw [(P₄ k hk i hi).2, e₃ k hk i hi]; exact Nat.mod_eq_of_lt (by have := B_lt i hi; omega)
  -- `H = (r⁴, r³)` in each lane.
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₄', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₅ M₅ => ?_)
  · rw [h₄ k hk i hi]; have := B_lt i hi; have := A_lt hi; split <;> omega
  · rw [y₄ k hk i hi]; exact B_lt i hi
  let C4 := Limbs26.mul B B
  let C3 := Limbs26.mul (rA) B
  have yB₄ : ∀ k < 8, yl s₄ k = B := fun k hk =>
    fext (fun _ h => yl_ge _ _ h) (fun _ h => mul_ge _ _ h) (y₄ k hk)
  have e₅ : ∀ k < 8, ∀ i < 5, hv s₅ k i = (if k % 2 = 0 then C4 i else C3 i) := fun k hk i hi => by
    rw [M₅.h k hk i hi, yB₄ k hk]
    have hf : hv s₄ k = if k % 2 = 0 then B else rA := by
      split
      · exact fext (fun _ h => hv_ge _ _ h) (fun _ h => mul_ge _ _ h) fun i hi => by
          rw [h₄ k hk i hi, ite_eq_left ‹_›]
      · exact fext (fun _ h => hv_ge _ _ h) rA_ge fun i hi => by
          rw [h₄ k hk i hi, ite_eq_right ‹_›]
    rw [hf]; split <;> rfl
  have yv₅ : ∀ i < 5, (qz s₅ (yreg i) 0).toNat = B i := fun i hi => by
    rw [M₅.y i hi 0 (by decide), (P₄ 0 (by decide) i hi).2, e₃ 0 (by decide) i hi]
  -- `r` in `D`.
  refine WP.block_append (WP.mono (splitR_ok s₅) fun s₆ ⟨v₆, S₆⟩ => ?_)
  have v₆' := vec_trans (vec_trans v₄' M₅.vec) v₆
  have d₆ : ∀ i < 5, dv s₆ 0 i = rA i :=
    ((S₆ 0 (by decide)).1.congr (vec_gpr (vec_trans v₄' M₅.vec)).symm).eq rS
  -- `H = (r^(4-j), r^(4-j))` in lane `j`, `Y = (r⁴, 1)`.
  refine WP.block_append (WP.mono (spread_ok (ax v₆')) fun s₇ ⟨v₇, D₇⟩ => ?_)
  have v₇' := vec_trans v₆' v₇
  have hv₆ : ∀ k < 8, ∀ i < 5, hv s₆ k i = hv s₅ k i := fun k hk i hi => by
    simp only [hv]; rw [((S₆ k hk).2 i hi).1]
  have e₅0 : ∀ i < 5, hv s₅ 0 i = C4 i := fun i hi => by
    rw [e₅ 0 (by decide) i hi, ite_eq_left (show 0 % 2 = 0 from rfl)]
  have e₅1 : ∀ i < 5, hv s₅ 1 i = C3 i := fun i hi => by
    rw [e₅ 1 (by decide) i hi, ite_eq_right (show ¬ 1 % 2 = 0 by decide)]
  have C4_lt : ∀ i < 5, C4 i < 2 ^ 27 := fun i hi => by
    have := M₅.hb 0 (by decide) i hi; rwa [e₅0 i hi] at this
  have C3_lt : ∀ i < 5, C3 i < 2 ^ 27 := fun i hi => by
    have := M₅.hb 1 (by decide) i hi; rwa [e₅1 i hi] at this
  have B_ge : ∀ j, 4 ≤ j → B j = B 4 := fun j h => mul_ge rA rA h
  have C4_ge : ∀ j, 4 ≤ j → C4 j = C4 4 := fun j h => mul_ge B B h
  have C3_ge : ∀ j, 4 ≤ j → C3 j = C3 4 := fun j h => mul_ge rA B h
  have h₇ : ∀ k < 8, ∀ i < 5, hv s₇ k i = quad C4 C3 B rA k i := fun k hk i hi => by
    rw [(D₇ k hk i hi).1, hv₆ 0 (by decide) i hi, hv₆ 1 (by decide) i hi, e₅0 i hi, e₅1 i hi,
      ((S₆ 0 (by decide)).2 i hi).2, yv₅ i hi, d₆ i hi, quad_apply]
  have y₇ : ∀ k < 8, ∀ i < 5, yl s₇ k i = alt C4 one k i := fun k hk i hi => by
    simp only [yl]; rw [(D₇ k hk i hi).2, hv₆ 0 (by decide) i hi, e₅0 i hi, alt_apply]
    split
    · exact Nat.mod_eq_of_lt (by have := C4_lt i hi; omega)
    · exact Nat.mod_eq_of_lt (Nat.lt_trans one_lt (by decide))
  have X_lt : ∀ k < 8, ∀ i < 5, quad C4 C3 B rA k i < 2 ^ 27 := fun k hk i hi => by
    rw [quad_apply]
    have := C4_lt i hi; have := C3_lt i hi; have := B_lt i hi; have := A_lt hi
    split <;> [omega; split <;> [omega; split <;> omega]]
  -- `H = r^(8 - π k)` in quadword `k`.
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₇', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₈ M₈ => ?_)
  · rw [h₇ k hk i hi]; have := X_lt k hk i hi; omega
  · rw [y₇ k hk i hi, alt_apply]; split
    · exact C4_lt i hi
    · exact one_lt
  -- `Y`: `r⁸` and `r^(8 - π k)`.
  refine WP.mono (finishY_ok fun k hk i hi => by have := M₈.hb k hk i hi; omega) fun s₉ ⟨v₉, F₉⟩ => ?_
  refine ⟨vec_trans (vec_trans v₇' M₈.vec) v₉, ?_⟩
  -- Values and bounds of the powers.
  have q₁ : Limbs26.val rA ≡ rN s [MOD P] := by rw [rS.val]
  have q₂ : Limbs26.val B ≡ rN s ^ 2 [MOD P] := by
    rw [show rN s ^ 2 = rN s * rN s by ring]; exact mul_modEq q₁ q₁
  have q₄ : Limbs26.val C4 ≡ rN s ^ 4 [MOD P] := by
    rw [show rN s ^ 4 = rN s ^ 2 * rN s ^ 2 by ring]; exact mul_modEq q₂ q₂
  have q₃ : Limbs26.val C3 ≡ rN s ^ 3 [MOD P] := by
    rw [show rN s ^ 3 = rN s * rN s ^ 2 by ring]; exact mul_modEq q₁ q₂
  have qX : ∀ k < 8, Limbs26.val (quad C4 C3 B rA k) ≡ rN s ^ (4 - k / 2) [MOD P] := fun k hk => by
    rcases (by omega : k / 2 = 0 ∨ k / 2 = 1 ∨ k / 2 = 2 ∨ k / 2 = 3) with h | h | h | h <;>
      simp only [quad, h, ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 2 by decide]
    · exact q₄
    · exact q₃
    · exact q₂
    · rw [show 4 - 3 = 1 from rfl, Nat.pow_one]; exact q₁
  have e₈ : ∀ k < 8, hv s₈ k = Limbs26.mul (quad C4 C3 B rA k) (alt C4 one k) := fun k hk => by
    have hx : hv s₇ k = quad C4 C3 B rA k :=
      fext (fun _ h => hv_ge _ _ h) (quad_ge C4_ge C3_ge B_ge rA_ge k) (h₇ k hk)
    have hy : yl s₇ k = alt C4 one k :=
      fext (fun _ h => yl_ge _ _ h) (alt_ge (b := one) C4_ge (fun _ h => one_ge h) k) (y₇ k hk)
    exact fext (fun _ h => hv_ge _ _ h) (fun _ h => mul_ge _ _ h) fun i hi => by
      rw [M₈.h k hk i hi, hx, hy]
  have q₈ : ∀ k < 8, Limbs26.val (hv s₈ k) ≡ rN s ^ (8 - pi k) [MOD P] := fun k hk => by
    rw [e₈ k hk]
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
    · have e : 8 - pi k = (4 - k / 2) + 4 := by simp only [pi]; omega
      rw [alt_of_even h0, e, pow_add]
      exact mul_modEq (qX k hk) q₄
    · have e : 8 - pi k = 4 - k / 2 := by simp only [pi]; omega
      rw [alt_of_odd h0, e, ← Nat.mul_one (rN s ^ (4 - k / 2))]
      exact mul_modEq (qX k hk) (by rw [one_val])
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [val_congr (F₉ k hk · · |>.2.1)]
    have := q₈ 0 (by decide)
    rwa [show pi 0 = 0 from rfl] at this
  · rw [val_congr (F₉ k hk · · |>.2.2)]; exact q₈ k hk
  · rw [(F₉ k hk i hi).2.1]; exact M₈.hb 0 (by decide) i hi
  · rw [(F₉ k hk i hi).2.2]; exact M₈.hb k hk i hi

end VG.Proof.Poly1305.X86_64.Avx512

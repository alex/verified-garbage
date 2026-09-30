import VerifiedGarbage.Proof.MlDsa.X86.Sign.Base

/-!
# ML-DSA signing on x86 (32-bit): the parameter sets, and the layout

Untrusted: everything here is checked by Lean. What the proofs need of a
parameter set (`PS`), which the three parameter sets have (`PS.of`); and
the layout checks of a call (`(Y p).ok`, `(Y p).sep`, …), which the tactic
`lay` proves from those facts by `omega`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-- What the proofs need of a parameter set. -/
structure PS (p : Params) : Prop where
  hk : 4 ≤ p.k ∧ p.k ≤ 8
  hl : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  hsLen : sLen p = 96 ∨ sLen p = 128
  hskLen : p.skLen = 128 + sLen p * (p.ℓ + p.k) + 416 * p.k
  hcLen : cLen p = 32 ∨ cLen p = 48 ∨ cLen p = 64
  hzLen : zLen p = 576 ∨ zLen p = 640
  hsigLen : p.sigLen = cLen p + zLen p * p.ℓ + p.ω + p.k
  hw1 : p.k * w1Len p ≤ 1024
  hw1Len : w1Len p = 128 ∨ w1Len p = 192
  hω : p.ω ≤ 80
  hhint : (p.ω, p.k) ∈ hintParams
  hball : (cLen p, p.τ) ∈ ballParams
  hγ₁ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19
  hγ₂ : p.γ₂ ∈ gamma2s
  hη : (p.η, p.η) ∈ bitPackParams ∧ sLen p = 32 * bitlen (p.η + p.η) ∧ p.η < 2 ^ 32
  hz : (p.γ₁ - 1, p.γ₁) ∈ bitPackParams ∧ zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)
  ht0 : ((4095 : Nat), (4096 : Nat)) ∈ bitPackParams ∧ 416 = 32 * bitlen (4095 + 4096)
  hw1Max : w1Max p ∈ simpleBitPackBounds ∧ w1Len p = 32 * bitlen (w1Max p)
  hok : ParamsOk p
  hβ : 1 ≤ p.β ∧ p.β < p.γ₂ ∧ p.γ₁ < 2 ^ 20 ∧ p.γ₂ < 2 ^ 20
  hscr : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)

theorem PS.of {p : Params} (h : Ok3 p) : PS p := by
  rcases h with rfl | rfl | rfl <;>
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel, rfl⟩

/-- The layout, as numbers. -/
theorem Y_n (p : Params) : (Y p).n = 5 := rfl
theorem Y_alen0 (p : Params) : (Y p).alen 0 = p.skLen := rfl
theorem Y_alen1 (p : Params) : (Y p).alen 1 = 64 := rfl
theorem Y_alen2 (p : Params) : (Y p).alen 2 = 32 := rfl
theorem Y_alen3 (p : Params) : (Y p).alen 3 = p.sigLen := rfl
theorem Y_alen4 (p : Params) : (Y p).alen 4 = scrLen p := rfl
theorem Y_awr0 (p : Params) : (Y p).awr 0 = false := rfl
theorem Y_awr1 (p : Params) : (Y p).awr 1 = false := rfl
theorem Y_awr2 (p : Params) : (Y p).awr 2 = false := rfl
theorem Y_awr3 (p : Params) : (Y p).awr 3 = true := rfl
theorem Y_awr4 (p : Params) : (Y p).awr 4 = true := rfl

/-! ## The constants of each parameter set -/

theorem k44 : mlDsa44.k = 4 := rfl
theorem l44 : mlDsa44.ℓ = 4 := rfl
theorem k65 : mlDsa65.k = 6 := rfl
theorem l65 : mlDsa65.ℓ = 5 := rfl
theorem k87 : mlDsa87.k = 8 := rfl
theorem l87 : mlDsa87.ℓ = 7 := rfl
theorem ω44 : mlDsa44.ω = 80 := rfl
theorem ω65 : mlDsa65.ω = 55 := rfl
theorem ω87 : mlDsa87.ω = 75 := rfl
theorem sLen44 : sLen mlDsa44 = 96 := by decide +kernel
theorem sLen65 : sLen mlDsa65 = 128 := by decide +kernel
theorem sLen87 : sLen mlDsa87 = 96 := by decide +kernel
theorem cLen44 : cLen mlDsa44 = 32 := by decide +kernel
theorem cLen65 : cLen mlDsa65 = 48 := by decide +kernel
theorem cLen87 : cLen mlDsa87 = 64 := by decide +kernel
theorem zLen44 : zLen mlDsa44 = 576 := by decide +kernel
theorem zLen65 : zLen mlDsa65 = 640 := by decide +kernel
theorem zLen87 : zLen mlDsa87 = 640 := by decide +kernel
theorem w1Len44 : w1Len mlDsa44 = 192 := by decide +kernel
theorem w1Len65 : w1Len mlDsa65 = 128 := by decide +kernel
theorem w1Len87 : w1Len mlDsa87 = 128 := by decide +kernel
theorem skLen44 : mlDsa44.skLen = 2560 := by decide +kernel
theorem skLen65 : mlDsa65.skLen = 4032 := by decide +kernel
theorem skLen87 : mlDsa87.skLen = 4896 := by decide +kernel
theorem sigLen44 : mlDsa44.sigLen = 2420 := by decide +kernel
theorem sigLen65 : mlDsa65.sigLen = 3309 := by decide +kernel
theorem sigLen87 : mlDsa87.sigLen = 4627 := by decide +kernel
theorem scr44 : scrLen mlDsa44 = 77824 := by decide +kernel
theorem scr65 : scrLen mlDsa65 = 103424 := by decide +kernel
theorem scr87 : scrLen mlDsa87 = 144384 := by decide +kernel

/-- The layout checks, for any of the three parameter sets `h3 : Ok3 p` of the context. -/
theorem Lay.sep_iff {Y : Lay} {b c : Buf} : Y.sep b c = true ↔
    (b.arg = c.arg ∧ (b.off + b.len ≤ c.off ∨ c.off + c.len ≤ b.off)) ∨
      (b.arg ≠ c.arg ∧ (Y.awr b.arg = true ∨ Y.awr c.arg = true)) := by
  unfold Lay.sep
  split <;> simp_all

macro "lay" : tactic => do
  let h := Lean.mkIdent `h3
  let e := Lean.mkIdent `h3e
  `(tactic| (
  rcases $h:ident with $e:ident | $e:ident | $e:ident <;> subst $e:ident <;>
  set_option linter.unusedSimpArgs false in
  simp only [Lay.okW_iff, Lay.ok_iff, Lay.sep_iff, Lay.apart, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Y_n, Y_alen0, Y_alen1, Y_alen2, Y_alen3,
    Y_alen4, Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4] <;>
  set_option linter.unusedSimpArgs false in
  simp only [oP, SC, oPS, oRS, oHIN, oMS, oCT, oW1, oST, oWK, oOK, oCNT, oKAP, oONES, skS1, skS2, skT0, sigZ, sigH,
    k44, l44, k65, l65, k87, l87, ω44, ω65, ω87, sLen44, sLen65, sLen87, cLen44, cLen65, cLen87,
    zLen44, zLen65, zLen87, w1Len44, w1Len65, w1Len87, skLen44, skLen65, skLen87, sigLen44, sigLen65, sigLen87,
    scr44, scr65, scr87, and_true, true_and, ne_eq, not_true_eq_false, false_and, or_false, true_or, or_true] at * <;>
  omega))

end VG.Proof.MlDsa.X86.Sign

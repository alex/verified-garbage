import VerifiedGarbage.Proof.MlDsa.X86.Sign.Base

/-!
# ML-DSA signing on x86 (32-bit): the parameter sets, and the layout

What the proofs need of a parameter set (`PS`), which the three parameter sets
have (`PS.of`); and the layout as numbers (`Y_n`, `Y_alen0`, …), from which
the tactic `ofs` (`Inv.lean`) proves the layout checks of a call by `omega`.
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

theorem Lay.sep_iff {Y : Lay} {b c : Buf} : Y.sep b c = true ↔
    (b.arg = c.arg ∧ (b.off + b.len ≤ c.off ∨ c.off + c.len ≤ b.off)) ∨
      (b.arg ≠ c.arg ∧ (Y.awr b.arg = true ∨ Y.awr c.arg = true)) := by
  unfold Lay.sep
  split <;> simp_all

end VG.Proof.MlDsa.X86.Sign

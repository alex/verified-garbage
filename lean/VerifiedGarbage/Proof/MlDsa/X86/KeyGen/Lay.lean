import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.KeyGen
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA key generation on x86 (32-bit): parameters and layout

Untrusted: everything here is checked by Lean. What the proof uses of a
parameter set (`PFacts`), the layout of key generation's arguments
(`YK p`: `seed`, `pk`, `sk` and `scratch`, and 96 bytes of stack), and the
tactic `lay`, which proves the checks of buffers against a layout (`Lay.ok`,
`Lay.sep`, `Lay.apart`, …) whose offsets depend on the parameters and on
indices, by unfolding them into arithmetic for `omega`.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k
  sw : scratchWords p = 128 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : PFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

/-- `seed` (32 bytes, read), `pk`, `sk` and `scratch` (written); 96 bytes of stack. -/
def YK (p : Params) : Lay := ⟨[(32, false), (p.pkLen, true), (p.skLen, true), (scrLen p, true)], 3, 96⟩

theorem YK_sc (p : Params) : (YK p).sc = kS := rfl
theorem YK_stk (p : Params) : (YK p).stk = 96 := rfl
theorem stkN {p : Params} {N : Nat} (h : N + 16 ≤ 96) : N + 16 ≤ (YK p).stk := h
theorem YK_n (p : Params) : (YK p).n = 4 := rfl
theorem YK_alen0 (p : Params) : (YK p).alen 0 = 32 := rfl
theorem YK_alen1 (p : Params) : (YK p).alen 1 = p.pkLen := rfl
theorem YK_alen2 (p : Params) : (YK p).alen 2 = p.skLen := rfl
theorem YK_alen3 (p : Params) : (YK p).alen 3 = scrLen p := rfl
theorem YK_awr0 (p : Params) : (YK p).awr 0 = false := rfl
theorem YK_awr1 (p : Params) : (YK p).awr 1 = true := rfl
theorem YK_awr2 (p : Params) : (YK p).awr 2 = true := rfl
theorem YK_awr3 (p : Params) : (YK p).awr 3 = true := rfl

/-- Unfolds checks of buffers against a layout into arithmetic, then `omega`. -/
syntax "lay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lay) => `(tactic| lay [])
  | `(tactic| lay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlKem.X86.Top.Lay.apart, VG.Proof.MlKem.X86.Top.Lay.ok,
        VG.Proof.MlKem.X86.Top.Lay.okW, VG.Proof.MlKem.X86.Top.Lay.sep, VG.Impl.MlDsa.X86.KeyGen.Arg.ok, VG.Impl.MlDsa.X86.KeyGen.sb,
        VG.Impl.MlDsa.X86.KeyGen.pB, VG.Impl.MlDsa.X86.KeyGen.aB, VG.Impl.MlDsa.X86.KeyGen.sB,
        VG.Impl.MlDsa.X86.KeyGen.tB, VG.Impl.MlDsa.X86.KeyGen.t1B, VG.Impl.MlDsa.X86.KeyGen.t0B,
        VG.Impl.MlDsa.X86.KeyGen.ssB, VG.Impl.MlDsa.X86.KeyGen.kS,
        VG.Proof.MlDsa.X86.KeyGen.YK_n, VG.Proof.MlDsa.X86.KeyGen.YK_sc,
        VG.Proof.MlDsa.X86.KeyGen.YK_alen0, VG.Proof.MlDsa.X86.KeyGen.YK_alen1,
        VG.Proof.MlDsa.X86.KeyGen.YK_alen2, VG.Proof.MlDsa.X86.KeyGen.YK_alen3,
        VG.Proof.MlDsa.X86.KeyGen.YK_awr0, VG.Proof.MlDsa.X86.KeyGen.YK_awr1,
        VG.Proof.MlDsa.X86.KeyGen.YK_awr2, VG.Proof.MlDsa.X86.KeyGen.YK_awr3,
        List.all_cons, List.all_nil, List.length_cons, List.length_nil, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, Bool.and_true, Bool.true_and, Bool.true_or, Bool.or_true, true_and, and_true,
        true_or, or_true, ↓reduceIte, $ls,*]
      set_option linter.unusedSimpArgs false in
      all_goals try simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, VG.Impl.MlDsa.X86.KeyGen.oP,
        VG.Impl.MlDsa.X86.KeyGen.oSA, VG.Impl.MlDsa.X86.KeyGen.oSB, VG.Impl.MlDsa.X86.KeyGen.oHX,
        VG.Impl.MlDsa.X86.KeyGen.oKL, VG.Impl.MlDsa.X86.KeyGen.oACC, VG.Impl.MlDsa.X86.KeyGen.oSS,
        VG.Impl.MlDsa.X86.KeyGen.oT0, decide_eq_true_eq, $ls,*]
      all_goals (and_intros <;> omega_arith)))

/-- `lay`, with the facts of the parameter set `hF : PFacts p`, in each case of `η`. -/
syntax "layp " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| layp $hF) => `(tactic| layp $hF [])
  | `(tactic| layp $hF [$ls,*]) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl
      rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
        lay [hlen, ($hF).pk, ($hF).sk, ($hF).sw, $ls,*]))

end VG.Proof.MlDsa.X86.KeyGen

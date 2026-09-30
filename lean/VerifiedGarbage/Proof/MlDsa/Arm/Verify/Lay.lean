import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp
import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Verify
import VerifiedGarbage.Proof.MlDsa.Verify.Final

/-!
# ML-DSA verification on 32-bit ARM: its parameters, precondition and buffers

Untrusted: everything here is checked by Lean. The facts about the parameter
sets the proof uses (`VFacts`); the precondition of the shared contract,
evaluated (`VPre`, `vpre_of`); and the buffers of the function (`vlay`):
`scratch`, the stack, `pk`, `mu` and `sig`, of which only `scratch` (and the
stack) are written, and the inputs, only read, may overlap each other. `vsep`
proves the facts about the offsets of pointers into them by `omega`, for any
parameter set.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure VFacts (p : Params) : Prop where
  k : 4 ≤ p.k ∧ p.k ≤ 8
  l : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  pk : p.pkLen = 32 + 320 * p.k
  sig : p.sigLen = oHint p + (p.ω + p.k)
  hint : oHint p = p.ctildeLen + lenZ p * p.ℓ
  ct : (p.ctildeLen = 32 ∨ p.ctildeLen = 48 ∨ p.ctildeLen = 64)
  lz : (lenZ p = 576 ∨ lenZ p = 640)
  om : 55 ≤ p.ω ∧ p.ω ≤ 80
  w1 : p.k * w1Len p ≤ 1024 ∧ 0 < p.k * w1Len p ∧ encodable (BitVec.ofNat 32 (p.k * w1Len p)) = true
  w1l : w1Len p = 128 ∨ (w1Len p = 192 ∧ p.k ≤ 5)
  scr : 8192 + 1024 * (20 + 8 * p.k) ≤ scrLen p ∧ scrLen p < 2 ^ 32
  hp : (p.ω, p.k) ∈ Spec.MlDsa.hintParams
  bu : (p.γ₁ - 1, p.γ₁) ∈ Spec.MlDsa.bitPackParams ∧ lenZ p = 32 * Spec.MlDsa.bitlen (p.γ₁ - 1 + p.γ₁) ∧
    p.γ₁ < 2 ^ 32
  ball : (p.ctildeLen, p.τ) ∈ Spec.MlDsa.ballParams ∧ p.τ < 2 ^ 32
  g2 : p.γ₂ ∈ Spec.MlDsa.gamma2s ∧ p.γ₂ < 2 ^ 32
  sbp : w1Max p ∈ Spec.MlDsa.simpleBitPackBounds ∧ w1Len p = 32 * Spec.MlDsa.bitlen (w1Max p) ∧ w1Max p < 2 ^ 32
  nb : p.γ₁ - p.β < 2 ^ 32 ∧ 0 < p.γ₁ - p.β
  g1 : p.γ₁ ∈ Proof.MlDsa.Verify.gamma1s

theorem vfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The precondition -/

section
variable (σ : State)

abbrev vPk : BitVec 32 := σ.gpr .r0
abbrev vMu : BitVec 32 := σ.gpr .r1
abbrev vSg : BitVec 32 := σ.gpr .r2
abbrev vScr : BitVec 32 := σ.gpr .r3

end

/-- The precondition of `verifyContract` with `STK` bytes of stack. -/
structure VPre (p : Params) (STK : Nat) (σ : State) : Prop where
  stk : STK ≤ σ.sp.toNat
  rd : σ.rd = [regA (vPk σ) p.pkLen, regA (vMu σ) 64, regA (vSg σ) p.sigLen]
  wr : σ.wr = [regA (vScr σ) (scrLen p)]
  d_pc : (regA (vPk σ) p.pkLen).Disjoint (regA (vScr σ) (scrLen p))
  d_mc : (regA (vMu σ) 64).Disjoint (regA (vScr σ) (scrLen p))
  d_sc : (regA (vSg σ) p.sigLen).Disjoint (regA (vScr σ) (scrLen p))
  b_p : (below σ STK).Disjoint (regA (vPk σ) p.pkLen)
  b_m : (below σ STK).Disjoint (regA (vMu σ) 64)
  b_s : (below σ STK).Disjoint (regA (vSg σ) p.sigLen)
  b_c : (below σ STK).Disjoint (regA (vScr σ) (scrLen p))
  f_p : (vPk σ).toNat + p.pkLen ≤ 2 ^ 32
  f_m : (vMu σ).toNat + 64 ≤ 2 ^ 32
  f_s : (vSg σ).toNat + p.sigLen ≤ 2 ^ 32
  f_c : (vScr σ).toNat + scrLen p ≤ 2 ^ 32

theorem vpre_of {p : Params} {n : Nat} {σ : State} (h : (Spec.MlDsa.verifyContract p Arm.abi (n + 1)).pre σ) :
    VPre p (n + 1) σ := by
  sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-! ## The buffers -/

/-- `scratch` (0), the stack (1), `pk` (2), `mu` (3) and `sig` (4). -/
def vlay (p : Params) (STK : Nat) (σ : State) : Lay :=
  ⟨fun i => [vScr σ, σ.sp - BitVec.ofNat 32 STK, vPk σ, vMu σ, vSg σ].getD i 0,
    [scrLen p, STK, p.pkLen, 64, p.sigLen]⟩

theorem vlay_sizes (p : Params) (STK : Nat) (σ : State) :
    (vlay p STK σ).sizes = [scrLen p, STK, p.pkLen, 64, p.sigLen] := rfl

/-- The buffers written: `scratch` and the stack. -/
abbrev vWb : List Nat := [0, 1]

theorem vlay_ok {p : Params} {STK : Nat} {σ : State} (hp : VPre p STK σ) : OkW (vlay p STK σ) vWb := by
  have es : (⟨State.addr (σ.sp - BitVec.ofNat 32 STK), STK⟩ : Region) = below σ STK := by
    rw [addr_sub hp.stk]
  refine ⟨fun i hi => ?_, fun i hi j hj hij hw => ?_⟩
  · simp only [vlay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (σ.sp - BitVec.ofNat 32 STK).toNat + STK ≤ 2 ^ 32
      have := hp.stk; have := σ.sp.isLt; bv_omega
    · exact hp.f_p
    · exact hp.f_m
    · exact hp.f_s
  · simp only [vlay, List.length_cons, List.length_nil] at hi hj
    simp only [vWb, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [vlay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_c.symm
    · exact hp.d_pc.symm
    · exact hp.d_mc.symm
    · exact hp.d_sc.symm
    · rw [es]; exact hp.b_c
    · rw [es]; exact hp.b_p
    · rw [es]; exact hp.b_m
    · rw [es]; exact hp.b_s
    · exact hp.d_pc
    · rw [es]; exact hp.b_p.symm
    · exact hp.d_mc
    · rw [es]; exact hp.b_m.symm
    · exact hp.d_sc
    · rw [es]; exact hp.b_s.symm

/-- Decides a fact about offsets in the buffers, for any parameter set with
the facts `hF`. -/
syntax "vsep " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vsep $hF) => `(tactic| vsep $hF [])
  | `(tactic| vsep $hF [$ls,*]) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).pk
      have := ($hF).sig; have := ($hF).hint; have := ($hF).ct; have := ($hF).lz; have := ($hF).om
      have := ($hF).w1; have := ($hF).w1l
      try dsimp only [$ls,*]
      try dsimp only [sepB, sepAll, VG.Proof.MlDsa.Arm.KeyGen.inB, tri, ix, sc, pS, pH, pZ, pC, pT, pT2, pW, pW1, pA, oP, oSS, oSB, oB, oCT]
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [sepB, sepAll, VG.Proof.MlDsa.Arm.KeyGen.inB, vlay_sizes, List.getD_cons_zero,
        List.getD_cons_succ, List.length_cons, List.length_nil, List.all_cons, List.all_nil, tri, ix,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_true, Bool.true_and,
        true_and, and_true, true_or, or_true, Nat.zero_add, oP, oSS, oSB, oB, oCT, sc, pS, pH, pZ, pC, pT, pT2,
        pW, pW1, pA, false_or, or_false, decide_eq_true_iff, $ls,*]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.Arm.Verify

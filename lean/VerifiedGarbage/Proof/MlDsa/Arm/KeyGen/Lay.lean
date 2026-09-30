import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.CallPack
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.CallArith
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.CallSample
import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.KeyGen
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA key generation on 32-bit ARM: its parameters, precondition and buffers

Untrusted: everything here is checked by Lean. The facts about the parameter
sets the proof uses (`PFacts`); the precondition of the shared contract,
evaluated (`Pre`, `pre_of`); and the buffers of the function (`lay`):
`scratch`, the stack, `seed`, `pk` and `sk`, pairwise disjoint, of which all
but `seed` are written. `lsep` proves the facts about the offsets of
pointers into them (`sepB`, `inB`) by `omega`, for any parameter set.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  k : 4 ≤ p.k ∧ p.k ≤ 8
  l : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k
  encPk : encodable (BitVec.ofNat 32 p.pkLen) = true

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : PFacts p := by
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

theorem PFacts.scr {p : Params} (hF : PFacts p) : 1024 * (p.k * p.ℓ + p.ℓ + p.k + 3) + 36864 ≤ scrLen p ∧
    scrLen p < 2 ^ 32 := by
  have := hF.k; have := hF.l; have := hF.kl
  simp only [scrLen, scratchWords]; omega

theorem PFacts.lens {p : Params} (hF : PFacts p) : p.pkLen < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ oT0 p + 416 * p.k ≤ p.skLen := by
  have := hF.k; have := hF.l
  refine ⟨by rw [hF.pk]; omega, ?_, by rw [hF.sk]⟩
  rw [hF.sk]; rcases hF.eta with ⟨_, he⟩ | ⟨_, he⟩ <;> simp only [oT0, he] <;> omega

/-! ## The precondition -/

section
variable (σ : State)

abbrev pSeed : BitVec 32 := σ.gpr .r0
abbrev pPk : BitVec 32 := σ.gpr .r1
abbrev pSk : BitVec 32 := σ.gpr .r2
abbrev pScr : BitVec 32 := σ.gpr .r3

end

/-- The precondition of `keyGenContract` with `STK` bytes of stack. -/
structure Pre (p : Params) (STK : Nat) (σ : State) : Prop where
  stk : STK ≤ σ.sp.toNat
  rd : σ.rd = [regA (pSeed σ) 32]
  wr : σ.wr = [regA (pPk σ) p.pkLen, regA (pSk σ) p.skLen, regA (pScr σ) (scrLen p)]
  d_xp : (regA (pSeed σ) 32).Disjoint (regA (pPk σ) p.pkLen)
  d_xs : (regA (pSeed σ) 32).Disjoint (regA (pSk σ) p.skLen)
  d_xc : (regA (pSeed σ) 32).Disjoint (regA (pScr σ) (scrLen p))
  d_ps : (regA (pPk σ) p.pkLen).Disjoint (regA (pSk σ) p.skLen)
  d_pc : (regA (pPk σ) p.pkLen).Disjoint (regA (pScr σ) (scrLen p))
  d_sc : (regA (pSk σ) p.skLen).Disjoint (regA (pScr σ) (scrLen p))
  b_x : (below σ STK).Disjoint (regA (pSeed σ) 32)
  b_p : (below σ STK).Disjoint (regA (pPk σ) p.pkLen)
  b_s : (below σ STK).Disjoint (regA (pSk σ) p.skLen)
  b_c : (below σ STK).Disjoint (regA (pScr σ) (scrLen p))
  f_x : (pSeed σ).toNat + 32 ≤ 2 ^ 32
  f_p : (pPk σ).toNat + p.pkLen ≤ 2 ^ 32
  f_s : (pSk σ).toNat + p.skLen ≤ 2 ^ 32
  f_c : (pScr σ).toNat + scrLen p ≤ 2 ^ 32

theorem pre_of {p : Params} {n : Nat} {σ : State} (h : (Spec.MlDsa.keyGenContract p Arm.abi (n + 1)).pre σ) :
    Pre p (n + 1) σ := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-! ## The buffers -/

/-- `scratch` (0), the stack (1), `seed` (2), `pk` (3) and `sk` (4). -/
def lay (p : Params) (STK : Nat) (σ : State) : Lay :=
  ⟨fun i => [pScr σ, σ.sp - BitVec.ofNat 32 STK, pSeed σ, pPk σ, pSk σ].getD i 0,
    [scrLen p, STK, 32, p.pkLen, p.skLen]⟩

theorem lay_sizes (p : Params) (STK : Nat) (σ : State) :
    (lay p STK σ).sizes = [scrLen p, STK, 32, p.pkLen, p.skLen] := rfl

theorem lay_size0 (p : Params) (STK : Nat) (σ : State) : (lay p STK σ).size 0 = scrLen p := rfl

/-- The buffers written: all but `seed`. -/
abbrev kWb : List Nat := [0, 1, 3, 4]

theorem lay_ok {p : Params} {STK : Nat} {σ : State} (hp : Pre p STK σ) : OkW (lay p STK σ) kWb := by
  have es : (⟨State.addr (σ.sp - BitVec.ofNat 32 STK), STK⟩ : Region) = below σ STK := by
    rw [addr_sub hp.stk]
  refine ⟨fun i hi => ?_, fun i hi j hj hij _ => ?_⟩
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (σ.sp - BitVec.ofNat 32 STK).toNat + STK ≤ 2 ^ 32
      have := hp.stk; have := σ.sp.isLt; bv_omega
    · exact hp.f_x
    · exact hp.f_p
    · exact hp.f_s
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_c.symm
    · exact hp.d_xc.symm
    · exact hp.d_pc.symm
    · exact hp.d_sc.symm
    · rw [es]; exact hp.b_c
    · rw [es]; exact hp.b_x
    · rw [es]; exact hp.b_p
    · rw [es]; exact hp.b_s
    · exact hp.d_xc
    · rw [es]; exact hp.b_x.symm
    · exact hp.d_xp
    · exact hp.d_xs
    · exact hp.d_pc
    · rw [es]; exact hp.b_p.symm
    · exact hp.d_xp.symm
    · exact hp.d_ps
    · exact hp.d_sc
    · rw [es]; exact hp.b_s.symm
    · exact hp.d_xs.symm
    · exact hp.d_ps.symm

/-- Decides a fact about offsets in the buffers, for any parameter set with
the facts `hF`. -/
syntax "lsep " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lsep $hF) => `(tactic| lsep $hF [])
  | `(tactic| lsep $hF [$ls,*]) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).lens
      have := ($hF).eta; have := ($hF).pk; have := ($hF).sk
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [sepB, sepAll, inB, lay_sizes, List.getD_cons_zero,
        List.getD_cons_succ, List.length_cons, List.length_nil, List.all_cons, List.all_nil, tri, ix,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_true, Bool.true_and,
        true_and, and_true, true_or, or_true, Nat.zero_add, oP, oSS, oKL, oHX, oSA, oSB, oT0, $ls,*]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.Arm.KeyGen

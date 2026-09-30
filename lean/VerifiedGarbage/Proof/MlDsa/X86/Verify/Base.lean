import VerifiedGarbage.Proof.MlDsa.X86.Verify.Prim
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp
import VerifiedGarbage.Impl.MlDsa.X86.Verify.Verify
import VerifiedGarbage.Proof.MlDsa.Verify.Spec
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Norm
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak

/-!
# ML-DSA verification on x86 (32-bit): the setting

Untrusted: everything here is checked by Lean. Verification is proven for
any implementations of the primitives it calls that are verified against
their contracts (`PrimsOk`), as key generation (`Proof/MlDsa/X86/KeyGen/`):
the contract's precondition gives the layout of the arguments (`YV p`:
`pk`, `mu`, `sig` and `scratch`, and 96 bytes of stack; `pre_of`), and its
public data the pointers and the inputs, as bytes (`lkV`, `pub_of`). What
the proof uses of a parameter set is `VFacts`; `layv` proves the checks of
buffers against the layout.
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- Verified implementations of the primitives verification calls. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : Callee P.ntt (fun stk => Spec.MlDsa.nttContract X86.abi stk)
  invNtt : Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract X86.abi stk)
  mul : Callee P.mul (fun stk => Spec.MlDsa.mulContract X86.abi stk)
  mulAdd : Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract X86.abi stk)
  sub : Callee P.sub (fun stk => Spec.MlDsa.subContract X86.abi stk)
  rejNtt : Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract X86.abi stk)
  ball : Callee P.ball (fun stk => Spec.MlDsa.sampleInBallContract X86.abi stk)
  useHint : Callee P.useHint (fun stk => Spec.MlDsa.useHintContract X86.abi stk)
  simpleBitPack : Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract X86.abi stk)
  bitUnpack : Callee P.bitUnpack (fun stk => Spec.MlDsa.bitUnpackContract X86.abi stk)
  unpackT1 : Callee P.unpackT1 (fun stk => Spec.MlDsa.unpackT1Contract X86.abi stk)
  hintUnpack : Callee P.hintUnpack (fun stk => Spec.MlDsa.hintBitUnpackContract X86.abi stk)
  normLt : Callee P.normLt (fun stk => Spec.MlDsa.normLtContract X86.abi stk)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure VFacts (p : Params) : Prop where
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : 4 ≤ p.k * p.ℓ ∧ p.k * p.ℓ ≤ 56
  ct : 32 ≤ p.ctildeLen ∧ p.ctildeLen ≤ 64
  lz : 576 ≤ lenZ p ∧ lenZ p ≤ 640
  w1 : 128 ≤ w1Len p ∧ 512 ≤ p.k * w1Len p ∧ p.k * w1Len p ≤ 1024
  scr : 8192 + 1024 * (20 + 8 * p.k) ≤ scratchWords p * 8
  pk : p.pkLen = 32 + 320 * p.k
  sig : p.sigLen = p.ctildeLen + lenZ p * p.ℓ + p.ω + p.k
  sw : scratchWords p = 128 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)
  om : p.ω ≤ 80
  hint : (p.ω, p.k) ∈ Spec.MlDsa.hintParams
  ball : (p.ctildeLen, p.τ) ∈ Spec.MlDsa.ballParams
  g1 : p.γ₁ ∈ Proof.MlDsa.Verify.gamma1s
  bp : (p.γ₁ - 1, p.γ₁) ∈ Spec.MlDsa.bitPackParams ∧ lenZ p = 32 * Spec.MlDsa.bitlen (p.γ₁ - 1 + p.γ₁)
  beta : 0 < p.γ₁ - p.β ∧ p.γ₁ - p.β < 2 ^ 32
  g2 : p.γ₂ ∈ Spec.MlDsa.gamma2s
  sbp : w1Max p ∈ Spec.MlDsa.simpleBitPackBounds ∧ w1Len p = 32 * Spec.MlDsa.bitlen (w1Max p)

theorem vfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, rfl,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The layout -/

/-- The size of `scratch`, in bytes. -/
abbrev scrLenV (p : Params) : Nat := scratchWords p * 8

/-- `pk`, `mu` and `sig` (read), `scratch` (written); 96 bytes of stack. -/
def YV (p : Params) : Lay := ⟨[(p.pkLen, false), (64, false), (p.sigLen, false), (scrLenV p, true)], 3, 96⟩

theorem YV_sc (p : Params) : (YV p).sc = vS := rfl
theorem YV_stk (p : Params) : (YV p).stk = 96 := rfl
theorem stkV {p : Params} {N : Nat} (h : N + 16 ≤ 96) : N + 16 ≤ (YV p).stk := h
theorem YV_n (p : Params) : (YV p).n = 4 := rfl
theorem YV_alen0 (p : Params) : (YV p).alen 0 = p.pkLen := rfl
theorem YV_alen1 (p : Params) : (YV p).alen 1 = 64 := rfl
theorem YV_alen2 (p : Params) : (YV p).alen 2 = p.sigLen := rfl
theorem YV_alen3 (p : Params) : (YV p).alen 3 = scrLenV p := rfl
theorem YV_awr0 (p : Params) : (YV p).awr 0 = false := rfl
theorem YV_awr1 (p : Params) : (YV p).awr 1 = false := rfl
theorem YV_awr2 (p : Params) : (YV p).awr 2 = false := rfl
theorem YV_awr3 (p : Params) : (YV p).awr 3 = true := rfl

/-! ### Checks of buffers, as arithmetic -/

/-- The result, a word of `scratch`. -/
abbrev accB (Y : Lay) : Buf := ⟨Y.sc, oACC, 4⟩

theorem okS {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ scratchWords p * 8) :
    (YV p).ok ⟨3, o, l⟩ = true := Lay.ok_iff.mpr ⟨show 3 < 4 by decide, h₁, h₂⟩

theorem okWS {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ scratchWords p * 8) :
    (YV p).okW ⟨3, o, l⟩ = true := Lay.okW_iff.mpr ⟨okS h₁ h₂, rfl⟩

theorem okPk {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ p.pkLen) : (YV p).ok ⟨0, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 0 < 4 by decide, h₁, h₂⟩

theorem okMu {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ 64) : (YV p).ok ⟨1, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 1 < 4 by decide, h₁, h₂⟩

theorem okSig {p : Params} {o l : Nat} (h₁ : 0 < l) (h₂ : o + l ≤ p.sigLen) : (YV p).ok ⟨2, o, l⟩ = true :=
  Lay.ok_iff.mpr ⟨show 2 < 4 by decide, h₁, h₂⟩

theorem sepS {p : Params} {o₁ l₁ o₂ l₂ : Nat} (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (YV p).sep ⟨3, o₁, l₁⟩ ⟨3, o₂, l₂⟩ = true := by
  unfold Lay.sep
  simp only [ite_true, Bool.or_eq_true, decide_eq_true_eq]
  exact h

theorem sepRS {p : Params} {a o₁ l₁ o₂ l₂ : Nat} (ha : a < 3) : (YV p).sep ⟨a, o₁, l₁⟩ ⟨3, o₂, l₂⟩ = true := by
  unfold Lay.sep
  rw [ite_eq_right_iff.mpr fun h => absurd h (show a ≠ 3 by omega)]
  exact Bool.or_eq_true_iff.mpr (.inr rfl)

theorem sepSR {p : Params} {a o₁ l₁ o₂ l₂ : Nat} (ha : a < 3) : (YV p).sep ⟨3, o₁, l₁⟩ ⟨a, o₂, l₂⟩ = true := by
  unfold Lay.sep
  rw [ite_eq_right_iff.mpr fun h => absurd h (show 3 ≠ a by omega)]
  exact Bool.or_eq_true_iff.mpr (.inl rfl)

theorem apart_nil' {Y : Lay} {b : Buf} (h : Y.ok b = true) : Y.apart b [] = true := by
  simp [Lay.apart, h]

theorem apart_cons' {Y : Lay} {b c : Buf} {bs : List Buf} (h₁ : Y.apart b bs = true) (h₂ : Y.ok c = true)
    (h₃ : Y.sep b c = true) : Y.apart b (c :: bs) = true := by
  simp only [Lay.apart, List.all_cons, Bool.and_eq_true] at h₁ ⊢
  exact ⟨h₁.1, ⟨h₂, h₃⟩, h₁.2⟩

/-- Rows of `z` in the signature, and of `w₁` in `scratch`. -/
theorem mul_row {a i n : Nat} (hi : i < n) : a * i + a ≤ a * n := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- Proves checks of buffers against the layout (`ok`, `okW`, `sep`, `apart`),
from arithmetic on their offsets closed by `omega`, with the facts of the
parameter set `hF : VFacts p` and those in the context. -/
syntax "lv " term:max : tactic
macro_rules
  | `(tactic| lv $hF) => `(tactic| (
      try simp only [Bool.and_eq_true, VG.Proof.MlDsa.X86.Verify.accB, VG.Proof.MlDsa.X86.Verify.YV_sc,
        VG.Proof.MlDsa.X86.KeyGen.chk3]
      try and_intros
      repeat' (first
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_cons'
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.apart_nil'
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okWS | with_reducible apply VG.Proof.MlDsa.X86.Verify.okS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okPk | with_reducible apply VG.Proof.MlDsa.X86.Verify.okMu
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.okSig | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepRS
        | with_reducible apply VG.Proof.MlDsa.X86.Verify.sepSR)
      all_goals (
        have := ($hF).k; have := ($hF).l; have := ($hF).ct; have := ($hF).om; have := ($hF).lz
        have := ($hF).w1; have := ($hF).scr; have := ($hF).pk; have := ($hF).sig
        try simp only [VG.Impl.MlDsa.X86.Verify.oP, VG.Impl.MlDsa.X86.Verify.oSB, VG.Impl.MlDsa.X86.Verify.oB,
          VG.Impl.MlDsa.X86.Verify.oCT, VG.Impl.MlDsa.X86.Verify.oACC, VG.Impl.MlDsa.X86.Verify.oSS,
          VG.Impl.MlDsa.X86.Verify.oHint]
        omega_arith)))

/-! ## The inputs -/

section
variable (p : Params) (s₀ : State)

abbrev vPk : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen
abbrev vMu : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64
abbrev vSig : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨2, 0, p.sigLen⟩) p.sigLen

/-- What verification may leak, its inputs. -/
def lkV : List Byte := vPk p s₀ ++ vMu s₀ ++ vSig p s₀

/-- The result so far. -/
abbrev accV (s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sb oACC 4)) 32

end

/-- A piece of verification. -/
abbrev VP (p : Params) := Piece (TPre (YV p)) (TPub (YV p) (lkV p))

theorem inputs_pub {p : Params} {s₀ s₀' : State} (hq : TPub (YV p) (lkV p) s₀ s₀') :
    vPk p s₀ = vPk p s₀' ∧ vMu s₀ = vMu s₀' ∧ vSig p s₀ = vSig p s₀' := by
  have h := hq.2.2
  simp only [lkV] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [Proof.MlKem.bytesAt_length])
  obtain ⟨h₃, h₄⟩ := List.append_inj h₁ (by simp [Proof.MlKem.bytesAt_length])
  exact ⟨h₃, h₄, h₂⟩

/-! ## The contract -/

theorem pre_of {p : Params} {s₀ : State} (h : (Spec.MlDsa.verifyContract p X86.abi 96).pre s₀) :
    TPre (YV p) s₀ := by
  sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h17 h18 h19 h20 h21
  have c4 : ∀ i, i < (YV p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    rw [YV_n] at hi; omega
  refine ⟨h1, by rw [YV_stk]; omega, by rw [YV_n]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h21, ?_, by rw [YV_sc, YV_n]; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · simp [argR, Lay.alen, YV]
    · simp [argR, Lay.alen, YV]
    · simp [argR, Lay.alen, YV]
    · simp [YV, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    any_goals simp [YV, Lay.awr] at hw
    simp [argR, Lay.alen, YV, scrLenV]
  · rw [h4]; simp [gR, Lay.n, YV]
  · intro i hi j hj hne hw
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [YV_awr0, YV_awr1, YV_awr2, YV_awr3, Bool.or_false, Bool.or_true,
      Bool.false_eq_true] at hw
    all_goals simp only [argR, YV_alen0, YV_alen1, YV_alen2, YV_alen3, scrLenV]
    exacts [h5, h7, h9, h5.symm, h7.symm, h9.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [argR, gR, YV_n, YV_alen0, YV_alen1, YV_alen2, YV_alen3, scrLenV]
    · exact h6.symm
    · exact h8.symm
    · exact h10.symm
    · exact h11.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [argR, YV_alen0, YV_alen1, YV_alen2, YV_alen3, scrLenV]
    · exact h12
    · exact h13
    · exact h14
    · exact h15
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;>
      simp only [argR, YV_stk, YV_alen0, YV_alen1, YV_alen2, YV_alen3, scrLenV]
    · exact h17
    · exact h18
    · exact h19
    · exact h20
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [YV_alen0, YV_alen1, YV_alen2, YV_alen3, scrLenV]
    · exact h22
    · exact h23
    · exact h24
    · exact h25

theorem pub_of {p : Params} {s₀ s₀' : State} (h : (Spec.MlDsa.verifyContract p X86.abi 96).pub s₀ s₀') :
    TPub (YV p) (lkV p) s₀ s₀' := by
  sig_pub [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [YV_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lkV, vPk, vMu, vSig, addr0]
    exact Proof.MlDsa.KeyGen.leakBytes_inj e₂

end VG.Proof.MlDsa.X86.Verify

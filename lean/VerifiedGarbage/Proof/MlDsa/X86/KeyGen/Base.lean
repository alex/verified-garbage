import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mask32
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# ML-DSA key generation on x86 (32-bit): the setting

Untrusted: everything here is checked by Lean. Key generation is proven for
any implementations of the primitives it calls that are verified against
their contracts (`PrimsOk`), as ML-KEM's top-level functions on x86
(`Proof/MlKem/X86/`): the contract's precondition gives the layout of the
arguments (`pre_of`), and its public data the pointers and what key
generation may leak, as bytes (`lkK`, `pub_of`). `ξ` gives `(ρ, ρ′, K)`
(`hxOf`), which the body keeps in `scratch` (`KB`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- Verified implementations of the primitives key generation calls. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : Callee P.ntt (fun stk => Spec.MlDsa.nttContract X86.abi stk)
  invNtt : Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract X86.abi stk)
  mul : Callee P.mul (fun stk => Spec.MlDsa.mulContract X86.abi stk)
  mulAdd : Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract X86.abi stk)
  add : Callee P.add (fun stk => Spec.MlDsa.addContract X86.abi stk)
  rejNtt : Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract X86.abi stk)
  rejBounded : Callee P.rejBounded (fun stk => Spec.MlDsa.rejBoundedContract X86.abi stk)
  power2Round : Callee P.power2Round (fun stk => Spec.MlDsa.power2RoundContract X86.abi stk)
  simpleBitPack : Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract X86.abi stk)
  bitPack : Callee P.bitPack (fun stk => Spec.MlDsa.bitPackContract X86.abi stk)

section
variable (p : Params) (s₀ : State)

/-- `ξ`. -/
abbrev xiOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32
/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf : List Byte := Spec.MlDsa.H (xiOf s₀ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf : List Byte := (keyGenSeeds p (xiOf s₀)).1
abbrev rho'Of : List Byte := (keyGenSeeds p (xiOf s₀)).2.1
abbrev kOf : List Byte := (keyGenSeeds p (xiOf s₀)).2.2
/-- What key generation may leak, as bytes. -/
def lkK : List Byte := (keyGenLeak p (xiOf s₀)).map (BitVec.ofNat 8)
/-- The AND of the samplers' results. -/
abbrev accV (s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sb oACC 4)) 32

end

/-- A piece of key generation. -/
abbrev KP (p : Params) := Piece (TPre (YK p)) (TPub (YK p) (lkK p))

theorem addr0 (s₀ : State) (i : Nat) (l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-! ## The contract -/

theorem pre_of {p : Params} {s₀ : State} (h : (Spec.MlDsa.keyGenContract p X86.abi 96).pre s₀) :
    TPre (YK p) s₀ := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < (YK p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    rw [YK_n] at hi; omega
  refine ⟨h1, by rw [YK_stk]; omega, by rw [YK_n]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h24, ?_, by rw [YK_sc, YK_n]; decide⟩
  · intro i hi hw
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals simp [YK, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · simp [YK, Lay.awr] at hw
    all_goals simp [argR, Lay.alen, YK, scrLen]
  · rw [h4]; simp [gR, Lay.n, YK]
  · intro i hi j hj hne _
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [argR, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    exacts [h5, h6, h7, h5.symm, h9, h10, h6.symm, h9.symm, h12, h7.symm, h10.symm, h12.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [argR, gR, YK_n, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h8.symm
    · exact h11.symm
    · exact h13.symm
    · exact h14.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [argR, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h15
    · exact h16
    · exact h17
    · exact h18
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [argR, YK_stk, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h25
    · exact h26
    · exact h27
    · exact h28

theorem pub_of {p : Params} {s₀ s₀' : State} (h : (Spec.MlDsa.keyGenContract p X86.abi 96).pub s₀ s₀') :
    TPub (YK p) (lkK p) s₀ s₀' := by
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [YK_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lkK, xiOf, addr0]
    rw [e₂]

/-- Two runs agree on `ρ`, and on what each `RejBoundedPoly` of `ExpandS` leaks. -/
theorem TPub.leak {p : Params} {s₀ s₀' : State} (hq : TPub (YK p) (lkK p) s₀ s₀') :
    rhoOf p s₀ = rhoOf p s₀' ∧ ∀ r < p.ℓ + p.k, Spec.MlDsa.rejBoundedLeak p.η (Proof.MlDsa.KeyGen.seedS (rho'Of p s₀) r) =
      Spec.MlDsa.rejBoundedLeak p.η (Proof.MlDsa.KeyGen.seedS (rho'Of p s₀') r) :=
  Proof.MlDsa.KeyGen.keyGenLeak_split (Proof.MlDsa.KeyGen.keyGenLeak_bytes hq.2.2)

end VG.Proof.MlDsa.X86.KeyGen

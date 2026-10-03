import VerifiedGarbage.Proof.MlKem.X86.DecapsBody
import VerifiedGarbage.Proof.MlKem1024.X86.Kem
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_decaps`

Decapsulation (`Proof/MlKem/X86/DecapsBody.lean`) for ML-KEM-1024 (`L1024`):
the facts of its layout, computed from its offsets; the contract's
precondition implies `TPre (Y L1024)` (`pre_of`) and its public data `TPub`
(`pub_of`).
-/

namespace VG.Proof.MlKem1024.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Decaps

instance : DecOK L1024 where
  ct := by decide
  dec := by decide
  keep := by decide
  mul := by decide
  v := by decide

instance : CmpOK L1024 where
  ct := by decide
  sel := by decide

instance : DecapsOK L1024 where
  ekc := by decide
  ek4 := by decide
  aEM := by decide
  g := by decide
  aG := by decide
  j := by decide
  dJ := by simp only [Enc.safe, Enc.safeS]; decide
  dNil := by simp only [Enc.safe, Enc.safeS]; decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (Spec.MlKem1024.decapsContract X86.abi 88).pre s₀) : TPre (Y L1024) s₀ := by
  sig_pre [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, h19, h20, h21, h22, h23,
    h24, h25, h26, h27⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h19 h20 h21 h22 h23
  have c4 : ∀ i, i < (Y L1024).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h23, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L1024, Params.dkLen, Params.ctLen, mlKem1024]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne hw
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6,
      absurd hw (by decide), absurd rfl hne, h8, h9,
      h5.symm, h8.symm, absurd rfl hne, h11,
      h6.symm, h9.symm, h11.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h7.symm, h10.symm, h12.symm, h13.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h14, h15, h16, h17]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h24, h25, h26, h27]

theorem pub_of {s₀ s₀' : State} (h : (Spec.MlKem1024.decapsContract X86.abi 88).pub s₀ s₀') : TPub (Y L1024) (lk L1024) s₀ s₀' := by
  sig_pub [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · have e := VG.Proof.MlKem.map_toNat_inj e₂
    show dkRho L1024.p (dk L1024 s₀) = dkRho L1024.p (dk L1024 s₀')
    rw [dk_eq, dk_eq, addr0, addr0]
    exact e

/-- Memory with the arguments `0`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x10 else if a = 0x500d then 0x20 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.decaps (Spec.MlKem1024.decapsContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L1024) (by decide) (NoSp.of_all (by decide +kernel))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := post (by decide) hp hfin
    rw [dk_eq, ct_eq, addr0, addr0, addr0] at r
    exact r
  · let st := satState satMem [⟨0, 3168⟩, ⟨0x1000, 1568⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.Decaps

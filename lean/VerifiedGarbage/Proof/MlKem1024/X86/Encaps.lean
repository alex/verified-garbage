import VerifiedGarbage.Proof.MlKem.X86.EncapsBody
import VerifiedGarbage.Proof.MlKem1024.X86.Kem
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_encaps`

Encapsulation (`Proof/MlKem/X86/EncapsBody.lean`) for ML-KEM-1024 (`L1024`):
the facts of its layout, computed from its offsets; the contract's
precondition implies `TPre (Y L1024)` (`pre_of`) and its public data `TPub`
(`pub_of`).
-/

namespace VG.Proof.MlKem1024.X86.Encaps

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Encaps

instance : EncapsOK L1024 where
  ekc := by decide
  mc := by decide
  ek4 := by decide
  ct4 := by decide
  aEM := by decide
  hh := by decide
  aH := by decide
  g := by decide
  aG := by decide
  key := by decide
  ct := by decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  dCt := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by simp only [Enc.safe, Enc.safeS]; decide

theorem pre_of {s₀ : State} (h : (Spec.MlKem1024.encapsContract X86.abi 88).pre s₀) : TPre (Y L1024) s₀ := by
  sig_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, -, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h25 h26 h27 h28 h29 h30
  have c5 : ∀ i, i < (Y L1024).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h30, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L1024, Params.ekLen, Params.ctLen, mlKem1024]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6, h7,
      absurd hw (by decide), absurd rfl hne, h9, h10, h11,
      h5.symm, h9.symm, absurd rfl hne, h13, h14,
      h6.symm, h10.symm, h13.symm, absurd rfl hne, h16,
      h7.symm, h11.symm, h14.symm, h16.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h8.symm, h12.symm, h15.symm, h17.symm, h18.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22, h23]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h25, h26, h27, h28, h29]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h31, h32, h33, h34, h35]

theorem pub_of {s₀ s₀' : State} (h : (Spec.MlKem1024.encapsContract X86.abi 88).pub s₀ s₀') : TPub (Y L1024) (lk L1024) s₀ s₀' := by
  sig_pub [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [e₃, e₄, e₅, e₆, e₇]
  · have e := VG.Proof.MlKem.map_toNat_inj e₂
    show ekRho L1024.p (ek L1024 s₀) = ekRho L1024.p (ek L1024 s₀')
    rw [ek_eq, ek_eq, addr0, addr0]
    exact e

/-- Memory with the arguments `0`, `0x800`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x08 else if a = 0x500d then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5016 then 1
  else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.encaps (Spec.MlKem1024.encapsContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L1024) (by decide) (NoSp.of_all (by decide +kernel))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := post (by decide) hfin
    rw [ek_eq, msg_eq, addr0, addr0, addr0, addr0] at r
    exact r
  · let st := satState satMem [⟨0, 1568⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1568⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 20⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.Encaps

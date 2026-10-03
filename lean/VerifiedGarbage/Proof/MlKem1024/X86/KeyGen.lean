import VerifiedGarbage.Proof.MlKem.X86.KeyGenBody
import VerifiedGarbage.Impl.MlKem1024.X86.Kem
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_keygen`

Key generation (`Proof/MlKem/X86/KeyGenBody.lean`) for ML-KEM-1024
(`L1024`): the facts of its layout, computed from its offsets; the contract's
precondition implies `TPre (Y L1024)` (`pre_of`) and its public data `TPub`,
which includes `ρ` (`pub_of`).
-/

namespace VG.Proof.MlKem1024.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.KeyGen

instance : GOK L1024 where
  rs := by decide
  g := by decide

instance : PrfOK L1024 where
  sig := by decide
  nb := by decide
  hash := by decide
  prf := by decide

instance : KgRowOK L1024 where
  seed := by decide
  nb := by decide
  samp := by decide
  mask := by decide
  mul := by decide
  mul0 := by decide
  mulJ := by decide
  row := by decide

instance : FinOK L1024 where
  fin := by decide
  enc := by decide
  ek := by decide
  rho := by decide
  cp := by decide
  hh := by decide
  zk := by decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (Spec.MlKem1024.keyGenContract X86.abi 88).pre s₀) : TPre (Y L1024) s₀ := by
  sig_pre [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < (Y L1024).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h24, ?_, by decide⟩
  · intro i hi hw
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L1024, Params.ekLen, Params.dkLen, mlKem1024]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne _
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, h5, h6, h7, h5.symm, absurd rfl hne, h9, h10, h6.symm, h9.symm, absurd rfl hne, h12,
      h7.symm, h10.symm, h12.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h8.symm
    · exact h11.symm
    · exact h13.symm
    · exact h14.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h15
    · exact h16
    · exact h17
    · exact h18
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h25
    · exact h26
    · exact h27
    · exact h28

theorem pub_of {s₀ s₀' : State} (h : (Spec.MlKem1024.keyGenContract X86.abi 88).pub s₀ s₀') : TPub (Y L1024) (lk L1024) s₀ s₀' := by
  sig_pub [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lk, d, addr0]
    exact VG.Proof.MlKem.map_toNat_inj e₂

/-- Memory with the arguments `0`, `0x100`, `0x1000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.keyGen (Spec.MlKem1024.keyGenContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L1024) (NoSp.of_all (by decide +kernel))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := post (by decide) hp hfin
    have ez : Buf.addr s₀ ⟨0, 32, 32⟩ = (arg s₀ 0).setWidth 64 + 32 := Buf.addr_eq hp (by decide)
    simp only [d, z, addr0, ez, show Buf.addr s₀ ⟨1, 0, L1024.p.ekLen⟩ = (arg s₀ 1).setWidth 64 from addr0 s₀ 1,
      show Buf.addr s₀ ⟨2, 0, L1024.p.dkLen⟩ = (arg s₀ 2).setWidth 64 from addr0 s₀ 2] at r
    exact r
  · let st := satState satMem [⟨0, 64⟩]
      [⟨0x100, 1568⟩, ⟨0x1000, 3168⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.KeyGen

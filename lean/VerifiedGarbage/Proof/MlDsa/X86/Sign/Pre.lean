import VerifiedGarbage.Proof.MlDsa.X86.Sign.Final

/-!
# ML-DSA signing on x86 (32-bit): the contract

The contract's precondition implies the layout `Y p` of the arguments
(`pre_of`); its public data are the pointers and `signLeak`, which is
`signLeakT` (`pub_of`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece E0 retR)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

set_option linter.unusedSimpArgs false in
theorem pre_of {s₀ : State} (h : (signContract p X86.abi 96).pre s₀) : TPre (Y p) s₀ := by
  sig_pre [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d03, d04, d0g, d13, d14, d1g, d23, d24, d2g, d34, d3g, d4g, r0, r1, r2, r3, r4, rg,
    s0, s1, s2, s3, s4, sg, f0, f1, f2, f3, f4⟩ := h
  rw [Nat.mul_comm (scratchWords p) 8] at h4 d04 d14 d24 d34 d4g r4 s4 f4
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth h1]
  rw [hs] at s0 s1 s2 s3 s4 sg
  have c5 : ∀ i, i < (Y p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    rw [Y_n] at hi; omega
  refine ⟨h1, by show 16 ≤ 96; decide, by rw [Y_n]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sg, ?_, by show 4 < 5; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    all_goals exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [h4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), d03, d04, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd rfl hne, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), d13, d14, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd rfl hne, d23, d24, d03.symm, d13.symm, d23.symm, absurd rfl hne, d34, d04.symm, d14.symm, d24.symm, d34.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [d0g.symm, d1g.symm, d2g.symm, d3g.symm, d4g.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [r0, r1, r2, r3, r4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [s0, s1, s2, s3, s4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [f0, f1, f2, f3, f4]

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

theorem pub_of {s₀ s₀' : State} (h : (signContract p X86.abi 96).pub s₀ s₀') : SPub p s₀ s₀' := by
  sig_pub [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4⟩ := h
  refine ⟨⟨e₁, fun i hi => ?_, rfl⟩, ?_⟩
  · rw [Y_n] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [a0, a1, a2, a3, a4]
  · simp only [skOf, muOf, rndOf, bSk, bMu, bRnd, addr0, signLeakT_eq_signLeak]
    exact e₂

end VG.Proof.MlDsa.X86.Sign

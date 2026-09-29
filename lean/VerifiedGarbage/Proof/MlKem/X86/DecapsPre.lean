import VerifiedGarbage.Proof.MlKem.X86.EncV
import VerifiedGarbage.Impl.MlKem.X86.Decaps
import VerifiedGarbage.Spec.MlKem.Contract

/-!
# ML-KEM-768 on x86 (32-bit): the setting of `vg_mlkem768_decaps`

Untrusted: everything here is checked by Lean. The layout of the arguments
(`Y`: `dk`, `ct`, `key`, `scratch`, and the 88 bytes of stack), which the
contract's precondition implies (`pre_of`); the public data, `ρ`
(`pub_of`), which is that of the encapsulation key in `dk` (`rho_eq`); and
the values the body computes: `m'` (`mD`), and the inputs of the
re-encryption (`I`). `dk`, `ct` and the values computed from them are
irreducible, so that elaboration never evaluates their bytes.
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3_512)

/-- `dk` and `ct` (read), `key` and `scratch` (written); 88 bytes of stack. -/
def Y : Lay := ⟨[(2400, false), (1088, false), (32, true), (32768, true)], 3, 88⟩

section
variable (s₀ : State)
/-- `dk`. -/
@[irreducible] def dk : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 2400⟩) 2400
/-- `ct`. -/
@[irreducible] def ct : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 1088⟩) 1088
/-- What decaps may leak: `ρ`. -/
abbrev lk : List Byte := dkRho mlKem768 (dk s₀)
/-- `m' = K-PKE.Decrypt(dk_PKE, c)`. -/
@[irreducible] def mD : List Byte := decM (dk s₀) (ct s₀)
/-- The encapsulation key in `dk`. -/
@[irreducible] def ekD : List Byte := dkEk (dk s₀)
/-- `G(m' ‖ h)`, as 64 bytes. -/
@[irreducible] def krD : List Byte := sha3_512 (mD s₀ ++ dkH (dk s₀))
end

theorem dk_eq (s₀ : State) : dk s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 2400⟩) 2400 := by unfold dk; rfl
theorem ct_eq (s₀ : State) : ct s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 1088⟩) 1088 := by unfold ct; rfl
theorem mD_eq (s₀ : State) : mD s₀ = decM (dk s₀) (ct s₀) := by unfold mD; rfl
theorem ekD_eq (s₀ : State) : ekD s₀ = dkEk (dk s₀) := by unfold ekD; rfl
theorem krD_eq (s₀ : State) : krD s₀ = sha3_512 (mD s₀ ++ dkH (dk s₀)) := by unfold krD; rfl

/-- The inputs of the re-encryption. -/
abbrev I : Enc.Inp := ⟨ekD, mD, krD⟩

theorem hS : Enc.SOK Y := ⟨by decide, by decide, by decide, rfl⟩

/-- `ρ` of the encapsulation key in `dk`, which the contract lets decaps leak. -/
theorem rho_eq (dk : List Byte) : ekRho mlKem768 (dkEk dk) = dkRho mlKem768 dk := by
  simp only [ekRho, dkRho, dkEk, List.drop_take, List.drop_drop, List.take_take]
  rfl

theorem hρ : Enc.RhoPub Y lk I := fun s₀ s₀' _ _ hq => by
  show ekRho mlKem768 (ekD s₀) = ekRho mlKem768 (ekD s₀')
  rw [ekD_eq, ekD_eq, rho_eq, rho_eq]
  exact hq.2.2

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

theorem pre_of {s₀ : State} (h : (decapsContract X86.abi 88).pre s₀) : TPre Y s₀ := by
  sig_pre [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, h19, h20, h21, h22, h23,
    h24, h25, h26, h27⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h19 h20 h21 h22 h23
  have c4 : ∀ i, i < Y.n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
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
    all_goals simp [argR, Lay.alen, Y]
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

theorem pub_of {s₀ s₀' : State} (h : (decapsContract X86.abi 88).pub s₀ s₀') : TPub Y lk s₀ s₀' := by
  sig_pub [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · have e := Sample.map_toNat_inj e₂
    show dkRho mlKem768 (dk s₀) = dkRho mlKem768 (dk s₀')
    rw [dk_eq, dk_eq, addr0, addr0]
    exact e

end VG.Proof.MlKem.X86.Decaps

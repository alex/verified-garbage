import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.Extra
import VerifiedGarbage.Impl.MlKem.X86.KeyGen
import VerifiedGarbage.Spec.MlKem.Contract

/-!
# ML-KEM-768 on x86 (32-bit): the setting of `vg_mlkem768_keygen`

The layout of the arguments (`Y`: `seed`, `ek`, `dk`, `scratch`, and the 88
bytes of stack), which the contract's precondition implies (`pre_of`); the
public data, which includes `ρ` (`pub_of`); and `d`, `z` and the values the
body computes from them.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `seed` (64 bytes, read), `ek`, `dk` and `scratch` (written); 88 bytes of stack. -/
def Y : Lay := ⟨[(64, false), (1184, true), (2400, true), (32768, true)], 3, 88⟩

section
variable (s₀ : State)
/-- `d`. -/
abbrev d : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32
/-- `z`. -/
abbrev z : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 32, 32⟩) 32
/-- What keygen may leak: `ρ`. -/
abbrev lk : List Byte := kgRho (d s₀)
end

theorem addr0 (s₀ : State) (i : Nat) : Buf.addr s₀ ⟨i, 0, 32⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

theorem pre_of {s₀ : State} (h : (keyGenContract X86.abi 88).pre s₀) : TPre Y s₀ := by
  sig_pre [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < Y.n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
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
    all_goals simp [argR, Lay.alen, Y]
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

theorem pub_of {s₀ s₀' : State} (h : (keyGenContract X86.abi 88).pub s₀ s₀') : TPub Y lk s₀ s₀' := by
  sig_pub [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lk, d, addr0]
    exact Sample.map_toNat_inj e₂

end VG.Proof.MlKem.X86.KeyGen

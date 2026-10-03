import VerifiedGarbage.Proof.MlKem.X86.EncV
import VerifiedGarbage.Impl.MlKem.X86.Decaps

/-!
# ML-KEM on x86 (32-bit): the setting of decapsulation

The layout of the arguments (`Y L`: `dk`, `ct`, `key`, `scratch`, and the 88
bytes of stack), which each parameter set's contract implies; the public data,
`ρ`, which is that of the encapsulation key in `dk` (`KPke.ekRho_dkEk`); and
the values the body computes: `m'` (`mD`), and the inputs of the re-encryption
(`I`). `dk`, `ct` and the values computed from them are irreducible, so that
elaboration never evaluates their bytes.
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3_512)

/-- `dk` and `ct` (read), `key` and `scratch` (written); 88 bytes of stack. -/
def Y (L : KemLay) : Lay := ⟨[(L.p.dkLen, false), (L.p.ctLen, false), (32, true), (L.scratch, true)], 3, 88⟩

section
variable (L : KemLay) (s₀ : State)
/-- `dk`. -/
@[irreducible] def dk : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.dkLen⟩) L.p.dkLen
/-- `ct`. -/
@[irreducible] def ct : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, L.p.ctLen⟩) L.p.ctLen
/-- What decaps may leak: `ρ`. -/
abbrev lk : List Byte := dkRho L.p (dk L s₀)
/-- `m' = K-PKE.Decrypt(dk_PKE, c)`. -/
@[irreducible] def mD : List Byte := KPke.decM L.p (dk L s₀) (ct L s₀)
/-- The encapsulation key in `dk`. -/
@[irreducible] def ekD : List Byte := KPke.dkEk L.p (dk L s₀)
/-- `G(m' ‖ h)`, as 64 bytes. -/
@[irreducible] def krD : List Byte := sha3_512 (mD L s₀ ++ KPke.dkH L.p (dk L s₀))
end

section
variable (L : KemLay) (s₀ : State)
theorem dk_eq : dk L s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.dkLen⟩) L.p.dkLen := by unfold dk; rfl
theorem ct_eq : ct L s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, L.p.ctLen⟩) L.p.ctLen := by unfold ct; rfl
theorem mD_eq : mD L s₀ = KPke.decM L.p (dk L s₀) (ct L s₀) := by unfold mD; rfl
theorem ekD_eq : ekD L s₀ = KPke.dkEk L.p (dk L s₀) := by unfold ekD; rfl
theorem krD_eq : krD L s₀ = sha3_512 (mD L s₀ ++ KPke.dkH L.p (dk L s₀)) := by unfold krD; rfl
end

/-- The inputs of the re-encryption. -/
abbrev I (L : KemLay) : Enc.Inp := ⟨ekD L, mD L, krD L⟩

theorem hS (L : KemLay) : Enc.SOK L (Y L) := ⟨of_decide_eq_true rfl, rfl, rfl, rfl⟩

/-- `ρ` of the encapsulation key in `dk`, which the contract lets decaps leak. -/
theorem hρ (L : KemLay) : Enc.RhoPub L (Y L) (lk L) (I L) := fun s₀ s₀' _ _ hq => by
  show ekRho L.p (ekD L s₀) = ekRho L.p (ekD L s₀')
  rw [ekD_eq, ekD_eq, KPke.ekRho_dkEk, KPke.ekRho_dkEk]
  exact hq.2.2

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- `sc_taint`, for code with `scratch` at `(Y L).sc`. -/
macro "yd_taint" : tactic => `(tactic| ((try simp only [show ∀ L, (Y L).sc = 3 from fun _ => rfl]); sc_taint))

end VG.Proof.MlKem.X86.Decaps

import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith

/-!
# ML-DSA key generation and verification on AArch64: the layout registers

The proofs of `vg_mldsa*_keygen` and `vg_mldsa*_verify` use the framework of
`Proof/MlDsa/AArch64/Call/`: these functions keep the addresses of their
buffers in `bases`, which two runs agree on (`SameB`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64

/-- The registers the functions keep the addresses of their buffers in. -/
abbrev bases : List Reg := [.x25, .x26, .x27, .x28]

theorem bases_pres : ∀ r ∈ bases, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem bases_kept : ∀ r ∈ bases, r ∈ keptRegs := by decide

/-- The buffers of a layout are in the registers `bases`. -/
abbrev LayOk : List (Reg × Nat) → Prop := LayIn bases

/-- Two states whose layout registers and stack pointer agree. -/
abbrev SameB : State → State → Prop := SameIn bases

end VG.Proof.MlDsa.AArch64.KeyGen

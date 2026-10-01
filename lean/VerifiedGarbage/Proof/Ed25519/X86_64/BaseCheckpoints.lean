import VerifiedGarbage.Proof.Ed25519.X86_64.BaseCheckpoint15

namespace VG.Proof.Ed25519.X86_64
open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64

theorem baseCheckpoint_ok (i : Nat) (hi : i < 16) :
    baseCheckpoint i = powerPoint basePoint (16 * i) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact baseCheckpoint0_ok.symm
  · exact baseCheckpoint1_ok.symm
  · exact baseCheckpoint2_ok.symm
  · exact baseCheckpoint3_ok.symm
  · exact baseCheckpoint4_ok.symm
  · exact baseCheckpoint5_ok.symm
  · exact baseCheckpoint6_ok.symm
  · exact baseCheckpoint7_ok.symm
  · exact baseCheckpoint8_ok.symm
  · exact baseCheckpoint9_ok.symm
  · exact baseCheckpoint10_ok.symm
  · exact baseCheckpoint11_ok.symm
  · exact baseCheckpoint12_ok.symm
  · exact baseCheckpoint13_ok.symm
  · exact baseCheckpoint14_ok.symm
  · exact baseCheckpoint15_ok.symm

end VG.Proof.Ed25519.X86_64

import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure Keep (s s' : VG.AArch64.State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : VG.AArch64.State) : Keep s s := ⟨rfl,rfl,rfl⟩
theorem Keep.trans {s t u : VG.AArch64.State} (h : Keep s t) (k : Keep t u) : Keep s u :=
  ⟨k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩

def SavedVector (orig s : VG.AArch64.State) : Prop :=
  ∀ i < 11, vdword (s.v (savedVec i)) 0 = orig.gpr (savedReg i)

theorem savedVec_inj : ∀ i < 11, ∀ j < 11, savedVec i = savedVec j ↔ i = j := by decide

theorem savedVec_ne_ptrs : ∀ i < 11, savedVec i ≠ .v30 ∧ savedVec i ≠ .v31 := by decide

theorem savedVec_not_preserved : ∀ i < 11, ∀ r ∈ preservedV, r ≠ savedVec i := by decide

def Ptrs (s₀ s : VG.AArch64.State) : Prop :=
  vdword (s.v .v30) 0 = s₀.gpr .x0 ∧ vdword (s.v .v31) 0 = s₀.gpr .x1

def Lanes (s : VG.AArch64.State) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), s.gpr (laneReg i) = A[i]

theorem laneReg_inj : ∀ i < 25, ∀ j < 25, laneReg i = laneReg j ↔ i = j := by decide

theorem savedReg_inj : ∀ i < 11, ∀ j < 11, savedReg i = savedReg j ↔ i = j := by decide

theorem laneReg_ne_x30 : ∀ i < 25, laneReg i ≠ .x30 := by decide

end VG.Proof.Sha3.AArch64.Scalar.Boundary

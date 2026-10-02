import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.Matrix

/-! Memory initialization establishes the shared matrix representation invariant. -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.Spec.Argon2

theorem Initialized.represents {m : Mem} {base : Addr} {p : Params} {h0 : List Byte}
    (positive : 0 < p.lanes) (lanePositive : 0 < p.laneLen)
    (h : Initialized m base p.lanes p.laneLen p.lanes h0) :
    Proof.Argon2.Represents m base p.blocks (initMemory p h0).memory := by
  refine ⟨Proof.Argon2.initMemory_size p h0, ?_⟩
  intro k hk
  rw [Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk), Option.getD_some]
  unfold Proof.Argon2.matrixCell
  rw [Nat.mul_comm k 1024]
  exact h.spec positive lanePositive k hk

end VG.Proof.Argon2.AArch64.MemoryInit

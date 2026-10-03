import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit
import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime

/-!
# Constant time

The pointers and the count of blocks are public, and so is everything the
function computes from them (the batches, the counts of passes and rounds,
the addresses of the round keys): every address and branch.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64 (PublicRegs)

theorem encrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) Impl.TripleDes.AArch64.BitsliceNeon.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) Impl.TripleDes.AArch64.BitsliceNeon.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.TripleDes.AArch64.BitslicedNeon

import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

theorem pruneWord_ct (k : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (pruneWord k)) (fun a b => a.sp = b.sp) := by
  apply Whole.block_append_ct (Whole.block_append_ct
    (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) Whole.block_nil_ct) ?_)
    (Whole.frame_store_ct _ _ _)
  split
  · exact Whole.quiet_block_ct _ (by simp [pruneLow, addrs])
  · split
    · exact Whole.quiet_block_ct _ (by simp [pruneHigh, addrs])
    · exact Whole.block_nil_ct

theorem prune_sp_ct : RelCT isa (fun a b => a.sp = b.sp) (.block prune) (fun a b => a.sp = b.sp) :=
  Whole.flatMap_sp_ct _ _ (fun k _ => pruneWord_ct k)

end VG.Proof.Ed25519.Arm.PublicKey

import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit

/-!
# The DES block's 32-bit ARM code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here: the checks of each part (`Round.lean`, `Block.lean`)
and the literals of the functions that run the block (`Lit.lean`) read these
literals rather than evaluate the S-box leaves and bit permutations again.
-/

namespace VG

materialize_table Impl.CmacTripleDes.Arm.leaf 2 64
materialize_value Impl.CmacTripleDes.Arm.inputs

/-- Half `h`'s tree. -/
abbrev Proof.CmacTripleDes.Arm.sbCode (h : Nat) : List VG.Arm.Instr :=
  Impl.CmacTripleDes.Arm.mux h 6 0 .r0

materialize_table Proof.CmacTripleDes.Arm.sbCode 2
materialize_value Impl.CmacTripleDes.Arm.sboxes
materialize_value Impl.CmacTripleDes.Arm.output
materialize_value Impl.CmacTripleDes.Arm.ipCode
materialize_value Impl.CmacTripleDes.Arm.fpCode
materialize_code Impl.CmacTripleDes.Arm.block

end VG

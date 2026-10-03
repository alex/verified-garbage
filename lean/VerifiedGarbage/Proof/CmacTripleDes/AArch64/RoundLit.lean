import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit

/-!
# The DES block's AArch64 code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here: the checks of each part (`Round.lean`, `Block.lean`)
and the literals of the functions that run the block (`Lit.lean`) read these
literals rather than evaluate the S-box leaves and bit permutations again.
-/

namespace VG

materialize_table Impl.CmacTripleDes.AArch64.leaf 64
materialize_value Impl.CmacTripleDes.AArch64.inputs
materialize_value Impl.CmacTripleDes.AArch64.sboxes
materialize_value Impl.CmacTripleDes.AArch64.output
materialize_value Impl.CmacTripleDes.AArch64.ipCode
materialize_value Impl.CmacTripleDes.AArch64.fpCode
materialize_code Impl.CmacTripleDes.AArch64.block

end VG

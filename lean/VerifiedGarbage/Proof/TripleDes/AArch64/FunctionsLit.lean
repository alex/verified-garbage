import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
import VerifiedGarbage.Impl.TripleDes.AArch64.Block

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.AArch64.roundBody
materialize_value Impl.TripleDes.AArch64.blockLoad
materialize_value Impl.TripleDes.AArch64.blockStore

/-! The functions. -/

materialize_code Impl.TripleDes.AArch64.encryptBlock
materialize_code Impl.TripleDes.AArch64.decryptBlock
materialize_code Impl.TripleDes.AArch64.Key.expandKey

end VG

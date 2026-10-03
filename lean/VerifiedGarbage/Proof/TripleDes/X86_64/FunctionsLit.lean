import VerifiedGarbage.Proof.TripleDes.X86_64.SboxTable
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.X86_64.roundBody
materialize_value Impl.TripleDes.X86_64.blockLoad
materialize_value Impl.TripleDes.X86_64.blockStore

/-! The functions. -/

materialize_code Impl.TripleDes.X86_64.encryptBlock
materialize_code Impl.TripleDes.X86_64.decryptBlock
materialize_code Impl.TripleDes.X86_64.Key.expandKey

end VG

import VerifiedGarbage.Proof.TripleDes.X86.SboxTable
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Impl.TripleDes.X86.Ecb

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.X86.roundBody
materialize_value Impl.TripleDes.X86.blockLoad
materialize_value Impl.TripleDes.X86.finalSave

/-! The functions. -/

materialize_code Impl.TripleDes.X86.encryptBlock
materialize_code Impl.TripleDes.X86.decryptBlock
materialize_code Impl.TripleDes.X86.Key.expandKey
materialize_code Impl.TripleDes.X86.Ecb.encrypt
materialize_code Impl.TripleDes.X86.Ecb.decrypt

end VG

import VerifiedGarbage.Proof.TripleDes.Arm.SboxTable
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Impl.TripleDes.Arm.Ecb

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.Arm.roundBody
materialize_value Impl.TripleDes.Arm.blockLoad

/-! The functions. -/

materialize_code Impl.TripleDes.Arm.encryptBlock
materialize_code Impl.TripleDes.Arm.decryptBlock
materialize_code Impl.TripleDes.Arm.Key.expandKey
materialize_code Impl.TripleDes.Arm.Ecb.encrypt
materialize_code Impl.TripleDes.Arm.Ecb.decrypt

end VG

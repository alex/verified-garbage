import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Impl.TripleDes.Arm.Ecb

namespace VG

materialize_code Impl.TripleDes.Arm.encryptBlock
materialize_code Impl.TripleDes.Arm.decryptBlock
materialize_code Impl.TripleDes.Arm.Key.expandKey
materialize_code Impl.TripleDes.Arm.Ecb.encrypt
materialize_code Impl.TripleDes.Arm.Ecb.decrypt

end VG

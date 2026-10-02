import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
import VerifiedGarbage.Impl.TripleDes.AArch64.Ecb

namespace VG

materialize_code Impl.TripleDes.AArch64.encryptBlock
materialize_code Impl.TripleDes.AArch64.decryptBlock
materialize_code Impl.TripleDes.AArch64.Key.expandKey
materialize_code Impl.TripleDes.AArch64.Ecb.encrypt
materialize_code Impl.TripleDes.AArch64.Ecb.decrypt

end VG

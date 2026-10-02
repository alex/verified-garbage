import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Impl.TripleDes.X86.Ecb

namespace VG

materialize_code Impl.TripleDes.X86.encryptBlock
materialize_code Impl.TripleDes.X86.decryptBlock
materialize_code Impl.TripleDes.X86.Key.expandKey
materialize_code Impl.TripleDes.X86.Ecb.encrypt
materialize_code Impl.TripleDes.X86.Ecb.decrypt

end VG

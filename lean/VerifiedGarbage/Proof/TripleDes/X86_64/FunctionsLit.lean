import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Impl.TripleDes.X86_64.Ecb

namespace VG

materialize_code Impl.TripleDes.X86_64.encryptBlock
materialize_code Impl.TripleDes.X86_64.decryptBlock
materialize_code Impl.TripleDes.X86_64.Key.expandKey
materialize_code Impl.TripleDes.X86_64.Ecb.encrypt
materialize_code Impl.TripleDes.X86_64.Ecb.decrypt

end VG

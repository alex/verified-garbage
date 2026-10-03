import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey

namespace VG

materialize_code Impl.TripleDes.X86_64.encryptBlock
materialize_code Impl.TripleDes.X86_64.decryptBlock
materialize_code Impl.TripleDes.X86_64.Key.expandKey

end VG

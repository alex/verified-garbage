import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceSse.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceSse.decrypt

end VG

import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx2

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.decrypt

end VG

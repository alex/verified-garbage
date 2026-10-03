import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx512

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceAvx512.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceAvx512.decrypt

end VG

import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512

/-!
# ChaCha20 on X86_64: the code as literals
-/

namespace VG

materialize_code Impl.ChaCha20.X86_64.block
materialize_code Impl.ChaCha20.X86_64.Xor.xor
materialize_code Impl.ChaCha20.X86_64.Avx2.xor
materialize_code Impl.ChaCha20.X86_64.Avx512.xor

end VG

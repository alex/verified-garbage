import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X25519.X86_64

/-!
# X25519 on x86-64: the code as a literal

Untrusted: everything here is checked by Lean. The field arithmetic is
unrolled, so the kernel would build the instructions again in every check
that evaluates the code (constant time, `spSafe`, properties of every
instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

namespace VG

materialize_code Impl.X25519.X86_64.x25519

end VG

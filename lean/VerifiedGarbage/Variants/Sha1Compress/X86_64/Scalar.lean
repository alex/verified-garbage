import VerifiedGarbage.Proof.Sha1.X86_64.Variant

/-!
# SHA-1 compression on x86-64: the scalar implementation

A variant of `Sha1Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha1_compress`, in the baseline ISA.
-/

namespace VG.Variants.Sha1Compress.X86_64.Scalar

def variant : Proof.Sha1.X86_64.Compress := .scalar

end VG.Variants.Sha1Compress.X86_64.Scalar

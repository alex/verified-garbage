import VerifiedGarbage.Proof.Sha512.X86_64.Variant

/-!
# SHA-512 compression on x86-64: the scalar implementation

A variant of `Sha512Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha512_compress`, in the baseline ISA.
-/

namespace VG.Variants.Sha512Compress.X86_64.Scalar

def variant : Proof.Sha512.X86_64.Compress := .scalar

end VG.Variants.Sha512Compress.X86_64.Scalar

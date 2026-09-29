import VerifiedGarbage.Proof.Sha1.X86_64.Variant

/-!
# SHA-1 compression on x86-64: the scalar implementation

A variant of `Sha1Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha1_compress`, in the baseline ISA.
-/

namespace VG.Variants.Sha1Compress.X86_64.Scalar

def variant : Proof.Sha1.X86_64.Compress where
  callee := .scalar
  ok := Proof.Sha1.X86_64.Stream.scalar_ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := ""
  features := []

end VG.Variants.Sha1Compress.X86_64.Scalar

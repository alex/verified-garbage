import VerifiedGarbage.Proof.Sha256.X86_64.Variant

/-!
# SHA-256 compression on x86-64: the scalar implementation

A variant of `Sha256Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha256_compress`, in the baseline ISA.
-/

namespace VG.Variants.Sha256Compress.X86_64.Scalar

def variant : Proof.Sha256.X86_64.Compress where
  callee := .scalar
  ok := Proof.Sha256.X86_64.Stream.scalar_ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

end VG.Variants.Sha256Compress.X86_64.Scalar

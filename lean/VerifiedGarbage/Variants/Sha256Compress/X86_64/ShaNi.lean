import VerifiedGarbage.Proof.Sha256.X86_64.Variant

/-!
# SHA-256 compression on x86-64 with the SHA extensions

A variant of `Sha256Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha256_compress_shani`, which needs the SHA extensions and SSSE3.
-/

namespace VG.Variants.Sha256Compress.X86_64.ShaNi

def variant : Proof.Sha256.X86_64.Compress where
  callee := .shani
  ok := Proof.Sha256.X86_64.Stream.shani_ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_shani"
  features := ["sha", "ssse3"]

end VG.Variants.Sha256Compress.X86_64.ShaNi

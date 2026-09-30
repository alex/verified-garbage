import VerifiedGarbage.Proof.Sha512.X86_64.Variant

/-!
# SHA-512 compression on x86-64 with the SHA512 extension

A variant of `Sha512Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha512_compress_shani`, which needs the SHA512 extension, AVX and AVX2.
-/

namespace VG.Variants.Sha512Compress.X86_64.ShaNi

def variant : Proof.Sha512.X86_64.Compress where
  callee := .shani
  ok := Proof.Sha512.X86_64.Stream.shani_ok
  mxcsr := by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide)
  suffix := "_shani"
  features := ["avx", "avx2", "sha512"]

end VG.Variants.Sha512Compress.X86_64.ShaNi

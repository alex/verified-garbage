import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Md5
import VerifiedGarbage.Proof.Md5.X86_64.Avx512.Lit

/-!
# MD5 on x86-64 with AVX-512

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): MD5, with `vg_md5_compress_avx512`, which needs AVX, AVX512F and AVX512VL.
-/

namespace VG.Variants.MdHash.X86_64.Md5Avx512

/-- The compression function with AVX-512. -/
def compress : Proof.Md5.X86_64.Compress where
  callee := .avx512
  ok := Proof.Md5.X86_64.Stream.avx512_ok
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx512"
  features := ["avx", "avx512f", "avx512vl"]

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Md5.variant compress

end VG.Variants.MdHash.X86_64.Md5Avx512

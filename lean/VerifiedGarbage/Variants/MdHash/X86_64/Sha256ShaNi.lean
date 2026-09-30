import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256

/-!
# SHA-256 on x86-64 with the SHA extensions

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-256, with `vg_sha256_compress_shani`, which needs the SHA extensions and SSSE3.
-/

namespace VG.Variants.MdHash.X86_64.Sha256ShaNi

/-- The compression function with the SHA extensions. -/
def compress : Proof.Sha256.X86_64.Compress where
  callee := .shani
  ok := Proof.Sha256.X86_64.Stream.shani_ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_shani"
  features := ["sha", "ssse3"]

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Sha256.variant compress

end VG.Variants.MdHash.X86_64.Sha256ShaNi

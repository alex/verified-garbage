import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256

/-!
# SHA-256 on x86-64: the scalar compression function

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-256, with `vg_sha256_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.X86_64.Sha256

/-- The scalar compression function. -/
def compress : Proof.Sha256.X86_64.Compress where
  callee := .scalar
  ok := Proof.Sha256.X86_64.Stream.scalar_ok
  mxcsr := by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide)
  suffix := ""
  features := []

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Sha256.variant compress

end VG.Variants.MdHash.X86_64.Sha256

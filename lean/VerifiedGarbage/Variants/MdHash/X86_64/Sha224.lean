import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
import VerifiedGarbage.Variants.MdHash.X86_64.Sha256

/-!
# SHA-224 on x86-64: the scalar compression function

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-224, with `vg_sha256_compress`, in the
baseline ISA (`Variants/MdHash/X86_64/Sha256.lean`).
-/

namespace VG.Variants.MdHash.X86_64.Sha224

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha224.variant Variants.MdHash.X86_64.Sha256.compress

end VG.Variants.MdHash.X86_64.Sha224

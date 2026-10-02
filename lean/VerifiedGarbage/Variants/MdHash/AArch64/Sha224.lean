import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha224
import VerifiedGarbage.Proof.Sha256.AArch64.ScalarBackend

/-!
# SHA-224 on AArch64

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): SHA-224, with `vg_sha256_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.AArch64.Sha224

def variant : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha224.variant Proof.Sha256.AArch64.Scalar.backend

end VG.Variants.MdHash.AArch64.Sha224

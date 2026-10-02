import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha224
import VerifiedGarbage.Proof.Sha256.AArch64.Sha2Backend

/-!
# SHA-224 on AArch64 with the SHA-256 instructions

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): SHA-224, with `vg_sha256_compress_sha2`, using FEAT_SHA256.
-/

namespace VG.Variants.MdHash.AArch64.Sha224Sha2

def variant : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha224.variant Proof.Sha256.AArch64.Sha2.backend

end VG.Variants.MdHash.AArch64.Sha224Sha2

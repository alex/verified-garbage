import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256

/-!
# SHA-256 on AArch64

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): SHA-256, with `vg_sha256_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.AArch64.Sha256

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha256.variant

end VG.Variants.MdHash.AArch64.Sha256

import VerifiedGarbage.Proof.Sha512.AArch64.Sha3Backend
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512

/-!
# SHA-384 on AArch64

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): SHA-384, with `vg_sha512_compress`, using FEAT_SHA512.
-/

namespace VG.Variants.MdHash.AArch64.Sha384Sha3

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha384 Proof.Sha512.AArch64.Sha3.backend

end VG.Variants.MdHash.AArch64.Sha384Sha3

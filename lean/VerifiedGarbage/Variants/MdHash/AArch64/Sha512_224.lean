import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512

/-!
# SHA-512/224 on AArch64

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): SHA-512/224, with `vg_sha512_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.AArch64.Sha512_224

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_224

end VG.Variants.MdHash.AArch64.Sha512_224

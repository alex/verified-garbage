import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha1

/-!
# SHA-1 on AArch64

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): SHA-1, with `vg_sha1_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.AArch64.Sha1

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha1.variant

end VG.Variants.MdHash.AArch64.Sha1

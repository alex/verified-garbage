import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Md5

/-!
# MD5 on AArch64

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): MD5, with `vg_md5_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.AArch64.Md5

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Md5.variant

end VG.Variants.MdHash.AArch64.Md5

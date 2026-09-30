import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Md5

/-!
# MD5 on x86-64

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): MD5, with `vg_md5_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.X86_64.Md5

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Md5.variant

end VG.Variants.MdHash.X86_64.Md5

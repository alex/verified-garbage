import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
import VerifiedGarbage.Variants.MdHash.X86_64.Sha256ShaNi

/-!
# SHA-224 on x86-64 with the SHA extensions

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-224, with `vg_sha256_compress_shani`,
which needs the SHA extensions and SSSE3 (`Variants/MdHash/X86_64/Sha256ShaNi.lean`).
-/

namespace VG.Variants.MdHash.X86_64.Sha224ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha224.variant Variants.MdHash.X86_64.Sha256ShaNi.compress

end VG.Variants.MdHash.X86_64.Sha224ShaNi

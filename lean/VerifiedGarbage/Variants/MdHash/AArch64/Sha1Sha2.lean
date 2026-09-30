import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha1
import VerifiedGarbage.Proof.Sha1.AArch64.Sha2Backend

namespace VG.Variants.MdHash.AArch64.Sha1Sha2

def variant : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha1.variant Proof.Sha1.AArch64.Sha2.backend

end VG.Variants.MdHash.AArch64.Sha1Sha2

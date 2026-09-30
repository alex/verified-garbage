import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Proof.Sha256.AArch64.Sha2Backend

namespace VG.Variants.MdHash.AArch64.Sha256Sha2

def variant : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha256.variant Proof.Sha256.AArch64.Sha2.backend

end VG.Variants.MdHash.AArch64.Sha256Sha2

import VerifiedGarbage.Proof.Sha512.AArch64.ScalarBackend
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512

/-!
# SHA-512/256 on AArch64

A variant of `MdHash` on AArch64 (see `TCB/Emit.lean`): SHA-512/256, with `vg_sha512_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.AArch64.Sha512_256

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_256 Proof.Sha512.AArch64.Scalar.backend

end VG.Variants.MdHash.AArch64.Sha512_256

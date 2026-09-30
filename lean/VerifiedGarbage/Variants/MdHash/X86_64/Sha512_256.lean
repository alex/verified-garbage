import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-!
# SHA-512/256 on x86-64

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-512/256, with
`vg_sha512_compress`, in the baseline ISA.
-/

namespace VG.Variants.MdHash.X86_64.Sha512_256

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 .scalar

end VG.Variants.MdHash.X86_64.Sha512_256

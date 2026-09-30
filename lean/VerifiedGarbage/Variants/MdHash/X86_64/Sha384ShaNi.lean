import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-!
# SHA-384 on x86-64 with the SHA512 extension

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-384, with
`vg_sha512_compress_shani`, which needs the SHA512 extension, AVX and AVX2.
-/

namespace VG.Variants.MdHash.X86_64.Sha384ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha384 .shani

end VG.Variants.MdHash.X86_64.Sha384ShaNi

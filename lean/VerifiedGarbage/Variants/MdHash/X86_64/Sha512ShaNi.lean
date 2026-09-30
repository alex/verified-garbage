import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-!
# SHA-512 on x86-64 with the SHA512 extension

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-512, with
`vg_sha512_compress_shani`, which needs the SHA512 extension, AVX and AVX2.

It carries the streaming `update` and `finalize` made with it, which the
family shares.
-/

namespace VG.Variants.MdHash.X86_64.Sha512ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 .shani (Proof.Pbkdf2.Md.X86_64.Sha512.stream .shani)

end VG.Variants.MdHash.X86_64.Sha512ShaNi

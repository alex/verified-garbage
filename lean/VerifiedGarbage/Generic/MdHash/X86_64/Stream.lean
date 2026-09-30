import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# Streaming Merkle–Damgård hash functions on x86-64

A generic file (see `TCB/Emit.lean`): each variant's streaming `update` and
`finalize` made with its implementation of the compression function, named
with its suffix (e.g. `vg_sha256_update_shani`), when no other variant
shares them (`MdHash.stream`, built from the functions' `Api`s in
`Proof/Pbkdf2/Md/X86_64/Hashes/`: see the review note there). Those of a
hash function with one implementation, or shared by a family, are in its
registration file.
-/

namespace VG.Generic.MdHash.X86_64.Stream

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := v.stream

end VG.Generic.MdHash.X86_64.Stream

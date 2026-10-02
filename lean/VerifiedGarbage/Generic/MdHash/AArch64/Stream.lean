import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-!
# Streaming Merkle–Damgård hash functions on AArch64

A generic file (see `TCB/Emit.lean`): each variant's streaming `update` and
`finalize` made with its implementation of the compression function, named
with its suffix (e.g. `vg_sha256_update_sha2`). Those a family shares are carried by one member's variants (SHA-512's, for the
SHA-512 family); those of a hash function with one implementation (MD5) are
in its registration file.

The variant supplies each function's `Api` and its verified code
(`MdHash.stream`, a `StreamFn`), whose contract is the one the `Api` gives it
(`StreamFn.ofApi`, which this file passes on as the artifact's `ofApi`).
-/

namespace VG.Generic.MdHash.AArch64.Stream

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := v.stream.map fun f =>
  { f.api with
    name := f.api.name ++ v.suffix
    target := AArch64.target
    doc := f.api.doc
    code := f.code
    contract := f.contract
    stack := f.stack
    verified := f.verified
    ofSig := f.ofSig
    ofApi := f.ofApi
    spSafe := f.spSafe
    features := v.features }

end VG.Generic.MdHash.AArch64.Stream

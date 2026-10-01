import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# Streaming Merkle–Damgård hash functions on X86_64

A generic file (see `TCB/Emit.lean`): each variant's streaming `update` and
`finalize` made with its implementation of the compression function, named
with its suffix (e.g. `vg_sha256_update_shani`). Those a family shares are carried by one member's variants (SHA-512's, for the
SHA-512 family); those of a hash function with one implementation (MD5) are
in its registration file.

The variant supplies each function's `Api` and its verified code
(`MdHash.stream`, a `StreamFn`), whose contract is the one the `Api` gives
it (`StreamFn.ofApi`, which this file passes on as the artifact's
`ofApi`). **Review note**: the name, `sig` and `doc` are trusted, as they
tie the Rust caller to the contract: they are those of the function's `Api`
(in `Spec/`, reviewed with the contract), and the name ends with the
variant's suffix. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract, and the CPU features the implementation needs.
-/

namespace VG.Generic.MdHash.X86_64.Stream

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := v.stream.map fun f =>
  { f.api with
    name := f.api.name ++ v.suffix
    target := X86_64.target
    doc := f.api.doc
    code := f.code
    contract := f.contract
    stack := f.stack
    verified := f.verified
    ofSig := f.ofSig
    ofApi := f.ofApi
    spSafe := f.spSafe
    features := v.features }

end VG.Generic.MdHash.X86_64.Stream

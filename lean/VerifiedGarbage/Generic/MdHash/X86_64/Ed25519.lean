import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified

/-!
# Ed25519 (RFC 8032) on x86-64, over SHA-512

A generic file (see `TCB/Emit.lean`): `vg_ed25519_public_key`, which hashes
the seed with SHA-512's streaming functions made with the variant's
compression function (`Impl/Ed25519/X86_64/PublicKey.lean`), is emitted once
for each implementation of SHA-512's compression function (each SHA-512
variant of `MdHash` carries it, `MdHash.sha512`; the other hash functions'
variants give nothing), named with its suffix (e.g.
`vg_ed25519_public_key_shani`). **Review note**: `sig` and `doc` are
trusted, as they tie the Rust caller to the contract: they are those of the
function's `Api` (`Spec/Ed25519/Contract.lean`), and this file adds only
notes on the implementation. The emitter adds the `# Safety` items that
depend on the target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which
`ofSig` checks against the contract, and the CPU features the
implementation needs.
-/

namespace VG.Generic.MdHash.X86_64.Ed25519

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  match v.sha512 with
  | none => []
  | some c => [
    { Spec.Ed25519.publicKeyApi with
      name := Spec.Ed25519.publicKeyApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ed25519.publicKeyApi.doc (notes := ["Hashes the seed with `vg_sha512_init`, \
        `vg_sha512_update" ++ c.suffix ++ "` and `vg_sha512_finalize" ++ c.suffix ++ "`, keeping \
        the state and the digest in `scratch`, and encodes `[s]B` with \
        `vg_ed25519_scalar_base_precomputed`. The pruned scalar `s` is kept in a 56-byte stack \
        frame with the pointers and cleared before the frame is popped; the calls use the 16 \
        bytes below it."])
      code := Impl.Ed25519.X86_64.publicKey c.callee c.suffix
      contract := Spec.Ed25519.publicKeyContract X86_64.abi 72
      stack := 72
      verified := Proof.Ed25519.X86_64.PublicKey.publicKey_verified c
      spSafe := Proof.Ed25519.X86_64.PublicKey.publicKey_spSafe c
      features := c.features }]

end VG.Generic.MdHash.X86_64.Ed25519

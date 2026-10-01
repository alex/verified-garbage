import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Verified

/-!
# Ed25519 (RFC 8032) on x86-64, over SHA-512

Complete key derivation, cached-key signing, and verification are emitted
for every SHA-512 compression backend carried by `MdHash.sha512`. Each
operation includes its streaming hash calls and carries the backend's
suffix and CPU features. Other hash families emit no Ed25519 artifacts.

**Review note**: `sig` and `doc` are
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
      features := c.features },
    { Spec.Ed25519.verifyApi with
      name := Spec.Ed25519.verifyApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ed25519.verifyApi.doc (notes := ["Hashes R, the public key and the message with \
        the selected SHA-512 backend, reduces the challenge modulo L, and calls \
        `vg_ed25519_verify_equation`. The digest and zero-extended reduced challenge occupy \
        separate buffers in a 168-byte stack frame; calls use another 16 bytes below it."])
      code := Impl.Ed25519.X86_64.VerifyMessage.code c.callee c.suffix
      contract := Spec.Ed25519.verifyContract X86_64.abi 184
      stack := 184
      verified := Proof.Ed25519.X86_64.VerifyMessage.verified c
      spSafe := Proof.Ed25519.X86_64.VerifyMessage.spSafe c
      features := c.features },
    { Spec.Ed25519.signCachedApi with
      name := Spec.Ed25519.signCachedApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ed25519.signCachedApi.doc (notes := ["Computes all three SHA-512 hashes with \
        the selected backend, reduces the nonce and challenge, encodes the nonce point, \
        and computes the final scalar. The 248-byte stack frame holds the pruned scalar, \
        nonce prefix, nonce, challenge, digest and saved arguments; its secret buffers are \
        cleared before return. Calls use another 16 bytes below the frame."])
      code := Impl.Ed25519.X86_64.SignCached.code c.callee c.suffix
      contract := Spec.Ed25519.signCachedContract X86_64.abi 264
      stack := 264
      verified := Proof.Ed25519.X86_64.SignCached.verified c
      spSafe := Proof.Ed25519.X86_64.SignCached.spSafe c
      features := c.features }]

end VG.Generic.MdHash.X86_64.Ed25519

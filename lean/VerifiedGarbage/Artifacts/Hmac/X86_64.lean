import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Hmac.X86_64.Shared

/-!
# HMAC-SHA-256 (RFC 2104) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Hmac.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "hmac"
    name := "vg_hmac_sha256_init"
    sig := Spec.Hmac.initSha256Sig
    doc := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the \
      SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent \
      `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes \
      (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its \
      `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.\n\n\
      Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and \
      `key_len` may affect timing, not the key.\n\n\
      # Safety\n\n\
      * `key_len` must be at most 64.\n\
      * `inner` and `outer` must each be valid for reads and writes of 96 bytes.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These four regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its calls of `vg_sha256_compress` store their \
      return address (distinct Rust objects never do)."
    code := Impl.Hmac.X86_64.init
    contract := Spec.Hmac.initSha256Contract X86_64.abi 8
    verified := Proof.Hmac.X86_64.Shared.init },
  { target := X86_64.target
    module := "hmac"
    name := "vg_hmac_sha256_finalize"
    sig := Spec.Hmac.finalizeSha256Sig
    doc := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
      SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes \
      (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the \
      text under `K₀` in bytes 176 to 207 of `*scratch`.\n\n\
      Contract: `VG.Spec.Hmac.finalizeSha256Contract`. Constant time: only the pointers and \
      `count` may affect timing, not the states.\n\n\
      # Safety\n\n\
      * `inner` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `outer` must be valid for reads of 96 bytes.\n\
      * `scratch` must be valid for reads and writes of 240 bytes; its contents on return \
      are unspecified, apart from the MAC.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 16 bytes of stack below it, where its calls of `vg_sha256_finalize` (which \
      calls `vg_sha256_compress`) store their return addresses (distinct Rust objects never \
      do)."
    code := Impl.Hmac.X86_64.finalize
    contract := Spec.Hmac.finalizeSha256Contract X86_64.abi 16
    verified := Proof.Hmac.X86_64.Shared.finalize }]

end VG.Artifacts.Hmac.X86_64

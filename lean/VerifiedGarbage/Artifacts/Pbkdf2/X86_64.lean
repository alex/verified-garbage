import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Pbkdf2.X86_64
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Shared

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Pbkdf2.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "pbkdf2"
    name := "vg_pbkdf2_hmac_sha256_iterate"
    sig := Spec.Pbkdf2.iterateSha256Sig
    doc := "Runs `n` steps of PBKDF2-HMAC-SHA-256's iteration: if, for a 64-byte key `K₀`, the \
      SHA-256 streaming state in bytes 0 to 95 of `*key` represents `K₀ ⊕ ipad` and the one \
      in bytes 96 to 191 represents `K₀ ⊕ opad` (as `vg_hmac_sha256_init` leaves them), \
      repeats `U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u` and `T = *t`, \
      and leaves the final `T` in `*t` (RFC 8018, step 3 of `F`).\n\n\
      Contract: `VG.Spec.Pbkdf2.iterateSha256Contract`. Constant time: only the pointers and \
      `n` may affect timing, not the key, `U` or `T`.\n\n\
      # Safety\n\n\
      * `key` must be valid for reads of 192 bytes, and `u` for reads of 32 bytes.\n\
      * `t` must be valid for reads and writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 384 bytes; its contents on return \
      are unspecified.\n\
      * `t` and `scratch` must not overlap each other, `key` or `u`, and none of the four \
      regions may overlap the return address on the stack or the 8 bytes of stack below it, \
      where its calls of `vg_sha256_compress` store their return address (distinct Rust \
      objects never do)."
    code := Impl.Pbkdf2.X86_64.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8
    verified := Proof.Pbkdf2.X86_64.Shared.iterate }]

end VG.Artifacts.Pbkdf2.X86_64

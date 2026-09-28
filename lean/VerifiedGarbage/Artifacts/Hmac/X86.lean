import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.X86.Shared

/-!
# HMAC-SHA-256 (RFC 2104) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Hmac.X86

def artifacts : List Artifact := [
  { target := X86.target
    module := "hmac"
    name := "vg_hmac_sha256_init"
    sig := Spec.Hmac.initSha256Sig
    doc := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the \
      SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent \
      `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes \
      (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its \
      `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.\n\n\
      Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and \
      `key_len` may affect timing, not the key. The function overwrites its own arguments \
      on the stack (which the callee owns under cdecl).\n\n\
      # Safety\n\n\
      * `key_len` must be at most 64.\n\
      * `inner` and `outer` must each be valid for reads and writes of 96 bytes.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These four regions must not overlap each other or the arguments of the call, \
      `inner`, `outer` and `scratch` must not overlap its return address, and none of \
      them may wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.Hmac.X86.init
    contract := Spec.Hmac.initSha256Contract X86.abi
    verified := Proof.Hmac.X86.Shared.init },
  { target := X86.target
    module := "hmac"
    name := "vg_hmac_sha256_finalize"
    sig := Spec.Hmac.finalizeSha256OutSig
    doc := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
      SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes \
      (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the \
      text under `K₀` to `*out`.\n\n\
      Contract: `VG.Spec.Hmac.finalizeSha256OutContract`. Constant time: only the pointers and \
      `count` may affect timing, not the states. The function overwrites its own \
      arguments on the stack (which the callee owns under cdecl).\n\n\
      # Safety\n\n\
      * `inner` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `outer` must be valid for reads of 96 bytes.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 240 bytes; its contents on return \
      are unspecified.\n\
      * `inner`, `out` and `scratch` must not overlap each other, `outer` or the stack \
      frame of the call (the return address and the arguments); `outer` must not overlap \
      the arguments; and none of the four may wrap around the end of the address space \
      (distinct Rust objects never do)."
    code := Impl.Hmac.X86.finalize
    contract := Spec.Hmac.finalizeSha256OutContract X86.abi
    verified := Proof.Hmac.X86.Shared.finalize }]

end VG.Artifacts.Hmac.X86

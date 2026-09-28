import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha256.X86_64.Shared

/-!
# SHA-256 (FIPS 180-4) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha256.X86_64

def artifacts : List Artifact := [
  { Spec.Sha256.compressApi with
    target := X86_64.target
    doc := Spec.Sha256.compressApi.doc ["These three regions must not overlap each other, nor the \
      return address on the stack (distinct Rust objects never do)."]
    code := Impl.Sha256.X86_64.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress },
  { Spec.Sha256.initApi with
    target := X86_64.target
    doc := Spec.Sha256.initApi.doc ["It must not overlap the return address on the stack (a Rust \
      object never does)."]
    code := Impl.Sha256.X86_64.Stream.init
    contract := Spec.Sha256.initContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.init },
  { Spec.Sha256.updateApi with
    target := X86_64.target
    doc := Spec.Sha256.updateApi.doc ["These three regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its call of \
      `vg_sha256_compress` stores its return address (distinct Rust objects never do)."]
    code := Impl.Sha256.X86_64.Stream.update .scalar
    contract := Spec.Sha256.updateContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.update },
  { Spec.Sha256.finalizeApi with
    target := X86_64.target
    doc := Spec.Sha256.finalizeApi.doc ["These three regions must not overlap each other, the \
      return address on the stack, or the 8 bytes of stack below it, where its call of \
      `vg_sha256_compress` stores its return address (distinct Rust objects never do)."]
    code := Impl.Sha256.X86_64.Stream.finalize .scalar
    contract := Spec.Sha256.finalizeContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.finalize },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_compress_shani"
    sig := Spec.Sha256.compressSig
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2), with the SHA extensions: \
      updates the hash value `*state` with the `n` 64-byte blocks starting at `blocks`, in \
      order.\n\n\
      Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.ShaNi.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress_shani
    features := ["sha", "ssse3"] },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_update_shani"
    sig := Spec.Sha256.updateSig
    doc := "Absorbs data into a SHA-256 computation, with the SHA extensions: if the streaming \
      state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it then represents \
      that message followed by the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha256_compress_shani` stores \
      its return address (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.update .shani
    contract := Spec.Sha256.updateContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.update_shani
    features := ["sha", "ssse3"] },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_finalize_shani"
    sig := Spec.Sha256.finalizeSig
    doc := "Finishes a SHA-256 computation, with the SHA extensions: if the streaming state \
      `*state` represents a message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest \
      of that message to `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha256_compress_shani` stores \
      its return address (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.finalize .shani
    contract := Spec.Sha256.finalizeContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.finalize_shani
    features := ["sha", "ssse3"] }]

end VG.Artifacts.Sha256.X86_64

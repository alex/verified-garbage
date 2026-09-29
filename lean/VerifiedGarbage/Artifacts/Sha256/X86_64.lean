import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha256.X86_64.Shared

/-!
# SHA-256 (FIPS 180-4) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha256.X86_64

def artifacts : List Artifact := [
  { Spec.Sha256.compressApi with
    target := X86_64.target
    doc := Spec.Sha256.compressApi.doc
    code := Impl.Sha256.X86_64.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress },
  { Spec.Sha256.initApi with
    target := X86_64.target
    doc := Spec.Sha256.initApi.doc
    code := Impl.Sha256.X86_64.Stream.init
    contract := Spec.Sha256.initContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.init },
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
      return are unspecified."
    code := Impl.Sha256.X86_64.ShaNi.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress_shani
    features := ["sha", "ssse3"] }]

end VG.Artifacts.Sha256.X86_64

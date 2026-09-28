import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha1.AArch64.Shared

/-!
# SHA-1 (FIPS 180-4) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_compress"
    sig := Spec.Sha1.compressSig
    doc := "The SHA-1 compression function (FIPS 180-4 §6.1.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha1.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 20 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha1.AArch64.compress
    contract := Spec.Sha1.compressContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_init"
    sig := Spec.Sha1.initSig
    doc := "Starts a SHA-1 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha1.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha1.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 84 bytes."
    code := Impl.Sha1.AArch64.Stream.init
    contract := Spec.Sha1.initContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_update"
    sig := Spec.Sha1.updateSig
    doc := "Absorbs data into a SHA-1 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha1.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 84 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address around its calls of \
      `vg_sha1_compress` (distinct Rust objects never do)."
    code := Impl.Sha1.AArch64.Stream.update
    contract := Spec.Sha1.updateContract AArch64.abi 16
    verified := Proof.Sha1.AArch64.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_finalize"
    sig := Spec.Sha1.finalizeSig
    doc := "Finishes a SHA-1 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-1 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha1.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 84 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 20 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address around its calls of \
      `vg_sha1_compress` (distinct Rust objects never do)."
    code := Impl.Sha1.AArch64.Stream.finalize
    contract := Spec.Sha1.finalizeContract AArch64.abi 16
    verified := Proof.Sha1.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha1.AArch64

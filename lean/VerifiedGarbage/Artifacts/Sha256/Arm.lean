import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/-!
# SHA-256 (FIPS 180-4) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Sha256.Arm

def artifacts : List Artifact := [
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Spec.Sha256.compressSig
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, and none of them may wrap \
      around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.compress
    contract := Spec.Sha256.compressContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Spec.Sha256.initSig
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.Stream.init
    contract := Spec.Sha256.initContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Spec.Sha256.updateSig
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha256.Arm.Stream.update
    contract := Spec.Sha256.updateContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Spec.Sha256.finalizeSig
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha256.Arm.Stream.finalize
    contract := Spec.Sha256.finalizeContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha256.Arm

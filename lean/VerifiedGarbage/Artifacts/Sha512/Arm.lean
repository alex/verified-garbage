import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha512.Arm.Shared

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Sha512.Arm

def artifacts : List Artifact := [
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_compress"
    sig := Spec.Sha512.compressSig
    doc := "The SHA-512 compression function (FIPS 180-4 §6.4.2), shared by SHA-384, SHA-512, \
      SHA-512/224 and SHA-512/256: updates the hash value `*state` with the `n` 128-byte \
      blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha512.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes.\n\
      * `blocks` must be valid for reads of `128 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 224 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, and none of them may wrap \
      around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.compress
    contract := Spec.Sha512.compressContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha384_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-384 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-384 (`VG.Spec.Sha512.H0_384`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_384`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512 (`VG.Spec.Sha512.H0_512`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_224_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/224 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/224 (`VG.Spec.Sha512.H0_512_224`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_224`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_256_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/256 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/256 (`VG.Spec.Sha512.H0_512_256`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_256`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_update"
    sig := Spec.Sha512.updateSig
    doc := "Absorbs data into a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if \
      the streaming state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it \
      then represents that message followed by the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha512.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 192 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha512.Arm.Stream.update
    contract := Spec.Sha512.updateContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_finalize"
    sig := Spec.Sha512.finalizeSig
    doc := "Finishes a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
      streaming state `*state` represents a message of `count` bytes, hashed from an initial \
      hash value, writes the final hash value `H⁽ᴺ⁾` of that message (64 bytes) to `*out`. \
      The SHA-512 digest is all of it; the SHA-384, SHA-512/224 and SHA-512/256 digests are \
      its first 48, 28 and 32 bytes.\n\n\
      Contract: `VG.Spec.Sha512.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are \
      not supported.\n\
      * `state` must be valid for reads and writes of 192 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 64 bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha512.Arm.Stream.finalize
    contract := Spec.Sha512.finalizeContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha512.Arm

import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.ChaCha20.Arm.Shared
import VerifiedGarbage.Impl.ChaCha20.Arm.Xor

/-!
# The ChaCha20 block function (RFC 8439) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  { target := Arm.target
    module := "chacha20"
    name := "vg_chacha20_block"
    sig := Spec.ChaCha20.blockSig
    doc := "The ChaCha20 block function (RFC 8439 §2.3): writes the block function of the \
      16-word state `*state` (20 rounds, then the input state added word by word) to the \
      first 16 words of `*buf`.\n\n\
      Contract: `VG.Spec.ChaCha20.blockContract`. Constant time: only the pointers may affect \
      timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads of 64 bytes.\n\
      * `buf` must be valid for reads and writes of 256 bytes. On return its first 64 bytes \
      hold the result and the rest is unspecified.\n\
      * `buf` must not overlap `state`, and neither may wrap around the end of the address \
      space (no Rust object does)."
    code := Impl.ChaCha20.Arm.block
    contract := Spec.ChaCha20.blockContract Arm.abi
    verified := Proof.ChaCha20.Arm.Shared.block
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "chacha20"
    name := "vg_chacha20_xor"
    sig := Spec.ChaCha20.xorSig
    doc := "XORs the first `len` bytes of the ChaCha20 keystream of the 16-word state `*state` \
      (RFC 8439 §2.4: the block function of the state with its block counter, word 12, \
      advanced by 0, 1, … modulo 2³²) into the `len` bytes at `data`, calling \
      `vg_chacha20_block` for each 64 bytes.\n\n\
      Contract: `VG.Spec.ChaCha20.xorContract`. Constant time: only the pointers and `len` \
      may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes; its contents on return are \
      unspecified.\n\
      * `data` must be valid for reads and writes of `len` bytes.\n\
      * `buf` must be valid for reads and writes of 320 bytes; its contents on return are \
      unspecified.\n\
      * These three regions must not overlap each other, and none of them may wrap around the \
      end of the address space (distinct Rust objects never do)."
    code := Impl.ChaCha20.Arm.Xor.xor
    contract := Spec.ChaCha20.xorContract Arm.abi
    verified := Proof.ChaCha20.Arm.Shared.xor
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.Arm

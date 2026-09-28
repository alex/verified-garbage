import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.ChaCha20.AArch64.Shared

/-!
# The ChaCha20 block function (RFC 8439) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.ChaCha20.AArch64

def artifacts : List Artifact := [
  { target := AArch64.target
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
      * `buf` must not overlap `state`."
    code := Impl.ChaCha20.AArch64.block
    contract := Spec.ChaCha20.blockContract AArch64.abi
    verified := Proof.ChaCha20.AArch64.Shared.block
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.AArch64

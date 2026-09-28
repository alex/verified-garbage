import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20.X86.Shared

/-!
# The ChaCha20 block function (RFC 8439) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.ChaCha20.X86

def artifacts : List Artifact := [
  { target := X86.target
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
      * `buf` must not overlap `state`, the arguments or the return address on the stack, and \
      nothing may wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.ChaCha20.X86.block
    contract := Spec.ChaCha20.blockContract X86.abi
    verified := Proof.ChaCha20.X86.Shared.block }]

end VG.Artifacts.ChaCha20.X86

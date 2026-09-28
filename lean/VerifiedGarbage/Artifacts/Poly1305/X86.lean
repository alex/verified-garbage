import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Poly1305.X86.Shared

/-!
# Poly1305 (RFC 8439 §2.5) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Poly1305.X86

def artifacts : List Artifact := [
  { target := X86.target
    module := "poly1305"
    name := "vg_poly1305_init"
    sig := Spec.Poly1305.initSig
    doc := "Starts a Poly1305 computation (RFC 8439 §2.5): makes the streaming state `*state` \
      represent the empty message under the 32-byte one-time key `*key`.\n\n\
      Contract: `VG.Spec.Poly1305.initContract`. The streaming state is the accumulator \
      followed by the key (`VG.Spec.Poly1305.Repr`). Constant time: only the pointers may \
      affect timing, not the key.\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 128 bytes.\n\
      * `key` must be valid for reads of 32 bytes.\n\
      * `state` must not overlap `key`, the arguments or the return address on the stack, and \
      nothing may wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.Poly1305.X86.init
    contract := Spec.Poly1305.initContract X86.abi
    verified := Proof.Poly1305.X86.Shared.init },
  { target := X86.target
    module := "poly1305"
    name := "vg_poly1305_blocks"
    sig := Spec.Poly1305.blocksSig
    doc := "Absorbs whole blocks into a Poly1305 computation: if the streaming state `*state` \
      represents a message under a key, it then represents that message followed by the `n` \
      16-byte blocks at `blocks`, under the same key.\n\n\
      Contract: `VG.Spec.Poly1305.blocksContract`. Constant time: only the pointers and `n` \
      may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 128 bytes.\n\
      * `blocks` must be valid for reads of `16 * n` bytes.\n\
      * `state` must not overlap `blocks`, the arguments or the return address on the stack, \
      and nothing may wrap around the end of the address space (distinct Rust objects never \
      do)."
    code := Impl.Poly1305.X86.blocks
    contract := Spec.Poly1305.blocksContract X86.abi
    verified := Proof.Poly1305.X86.Shared.blocks },
  { target := X86.target
    module := "poly1305"
    name := "vg_poly1305_finalize"
    sig := Spec.Poly1305.finalizeTailSig
    doc := "Finishes a Poly1305 computation: if the streaming state `*state` represents a \
      message under a key, writes the tag of that message followed by the `len` bytes at \
      `tail`, under that key, to `*out`.\n\n\
      Contract: `VG.Spec.Poly1305.finalizeTailContract`. Constant time: only the pointers and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `len` must be less than 16.\n\
      * `state` must be valid for reads and writes of 128 bytes; its contents on return are \
      unspecified.\n\
      * `tail` must be valid for reads of `len` bytes.\n\
      * `out` must be valid for writes of 16 bytes.\n\
      * These three regions must not overlap each other, and `state` and `out` must not \
      overlap the arguments or the return address on the stack; nothing may wrap around the \
      end of the address space (distinct Rust objects never do)."
    code := Impl.Poly1305.X86.finalize
    contract := Spec.Poly1305.finalizeTailContract X86.abi
    verified := Proof.Poly1305.X86.Shared.finalize }]

end VG.Artifacts.Poly1305.X86

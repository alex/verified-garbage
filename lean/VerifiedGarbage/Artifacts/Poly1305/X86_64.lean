import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Poly1305.X86_64.Shared

/-!
# Poly1305 (RFC 8439 §2.5) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Poly1305.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "poly1305"
    name := "vg_poly1305_init"
    sig := Spec.Poly1305.initSig
    doc := "Starts a Poly1305 computation (RFC 8439 §2.5): makes the streaming state `*state` \
      represent the empty message under the 32-byte one-time key `*key`.\n\n\
      Contract: `VG.Spec.Poly1305.initContract`. The streaming state is the accumulator \
      followed by the key (`VG.Spec.Poly1305.Repr`), and the buffered bytes \
      (`VG.Spec.Poly1305.Buffered`). Constant time: only the pointers may affect timing, not \
      the key.\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 128 bytes.\n\
      * `key` must be valid for reads of 32 bytes.\n\
      * `state` must not overlap `key` or the return address on the stack (distinct Rust \
      objects never do)."
    code := Impl.Poly1305.X86_64.init
    contract := Spec.Poly1305.initContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.init },
  { target := X86_64.target
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
      * `state` must not overlap `blocks` or the return address on the stack, and `blocks` \
      must not wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.Poly1305.X86_64.blocks
    contract := Spec.Poly1305.blocksContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.blocks },
  { target := X86_64.target
    module := "poly1305"
    name := "vg_poly1305_update"
    sig := Spec.Poly1305.updateSig
    doc := "Absorbs bytes into a Poly1305 computation: if the streaming state `*state` \
      represents a message of `count` bytes (modulo 2⁶⁴) under a key, it then represents that \
      message followed by the `len` bytes at `data`, under the same key. The state buffers the \
      message's last bytes that do not fill a 16-byte block.\n\n\
      Contract: `VG.Spec.Poly1305.updateContract`. The streaming state is the accumulator of the \
      message's whole blocks, the key and the buffered bytes (`VG.Spec.Poly1305.Buffered`). \
      Constant time: only the pointers, `count` and `len` may affect timing, not the state or \
      the data.\n\n\
      # Safety\n\n\
      * `count` must be the length of the message `*state` represents, modulo 2⁶⁴: 0 after \
      `vg_poly1305_init`, plus the `len` of each call since.\n\
      * `state` must be valid for reads and writes of 128 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `state` must not overlap `data` or the return address on the stack, and `data` must \
      not wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.Poly1305.X86_64.update
    contract := Spec.Poly1305.updateContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.update },
  { target := X86_64.target
    module := "poly1305"
    name := "vg_poly1305_finalize"
    sig := Spec.Poly1305.finalizeSig
    doc := "Finishes a Poly1305 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴) under a key, writes the tag of that message under \
      that key to `*out`.\n\n\
      Contract: `VG.Spec.Poly1305.finalizeContract`. Constant time: only the pointers and \
      `count` may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `count` must be the length of the message `*state` represents, modulo 2⁶⁴ (see \
      `vg_poly1305_update`).\n\
      * `state` must be valid for reads and writes of 128 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 16 bytes.\n\
      * `state` and `out` must not overlap each other or the return address on the stack \
      (distinct Rust objects never do)."
    code := Impl.Poly1305.X86_64.finalize
    contract := Spec.Poly1305.finalizeContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.finalize }]

end VG.Artifacts.Poly1305.X86_64

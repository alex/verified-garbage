import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Poly1305.X86_64.Shared

/-!
# Poly1305 (RFC 8439 §2.5) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
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
      followed by the key (`VG.Spec.Poly1305.Repr`). Constant time: only the pointers may \
      affect timing, not the key.\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 128 bytes.\n\
      * `key` must be valid for reads of 32 bytes."
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
      * `blocks` must be valid for reads of `16 * n` bytes."
    code := Impl.Poly1305.X86_64.blocks
    contract := Spec.Poly1305.blocksContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.blocks },
  { target := X86_64.target
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
      * `out` must be valid for writes of 16 bytes."
    code := Impl.Poly1305.X86_64.finalize
    contract := Spec.Poly1305.finalizeTailContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.finalize }]

end VG.Artifacts.Poly1305.X86_64

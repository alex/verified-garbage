import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Poly1305.AArch64
import VerifiedGarbage.Proof.Poly1305.AArch64.Shared

/-!
# Poly1305 (RFC 8439 §2.5) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Poly1305.AArch64

def artifacts : List Artifact := [
  { target := AArch64.target
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
      * `state` must not overlap `key` (distinct Rust objects never do)."
    code := Impl.Poly1305.AArch64.init
    contract := Spec.Poly1305.initContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
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
      * `state` must not overlap `blocks`, and `blocks` must not wrap around the end of the \
      address space (distinct Rust objects never do)."
    code := Impl.Poly1305.AArch64.blocks
    contract := Spec.Poly1305.blocksContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Shared.blocks
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
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
      * These three regions must not overlap each other (distinct Rust objects never do)."
    code := Impl.Poly1305.AArch64.finalize
    contract := Spec.Poly1305.finalizeTailContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Poly1305.AArch64

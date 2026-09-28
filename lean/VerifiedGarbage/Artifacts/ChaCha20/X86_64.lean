import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.ChaCha20.X86_64.Shared
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor

/-!
# The ChaCha20 block function (RFC 8439) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := X86_64.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.X86_64.block
    contract := Spec.ChaCha20.blockContract X86_64.abi
    verified := Proof.ChaCha20.X86_64.Shared.block },
  { target := X86_64.target
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
      unspecified."
    code := Impl.ChaCha20.X86_64.Xor.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 8
    writeArgs := true
    stack := 8
    verified := Proof.ChaCha20.X86_64.Shared.xor }]

end VG.Artifacts.ChaCha20.X86_64

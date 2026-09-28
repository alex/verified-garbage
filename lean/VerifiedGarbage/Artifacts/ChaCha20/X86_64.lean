import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Shared

/-!
# The ChaCha20 keystream XOR (RFC 8439 §2.4) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact := [
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
      unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its calls of `vg_chacha20_block` store their \
      return address, and none of them may wrap around the end of the address space \
      (distinct Rust objects never do)."
    code := Impl.ChaCha20.X86_64.Xor.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 8
    verified := Proof.ChaCha20.X86_64.Shared.xor }]

end VG.Artifacts.ChaCha20.X86_64

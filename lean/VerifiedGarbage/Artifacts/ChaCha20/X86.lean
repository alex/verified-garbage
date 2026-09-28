import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20.X86.Shared
import VerifiedGarbage.Impl.ChaCha20.X86.Xor

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
    verified := Proof.ChaCha20.X86.Shared.block },
  { target := X86.target
    module := "chacha20"
    name := "vg_chacha20_xor"
    sig := Spec.ChaCha20.xorSig
    doc := "XORs the first `len` bytes of the ChaCha20 keystream of the 16-word state `*state` \
      (RFC 8439 §2.4: the block function of the state with its block counter, word 12, \
      advanced by 0, 1, … modulo 2³²) into the `len` bytes at `data`, calling \
      `vg_chacha20_block` for each 64 bytes.\n\n\
      Contract: `VG.Spec.ChaCha20.xorContract`. Constant time: only the pointers and `len` \
      may affect timing, not the state or the data. The function may overwrite its own \
      arguments on the stack (which the callee owns under cdecl).\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes; its contents on return are \
      unspecified.\n\
      * `data` must be valid for reads and writes of `len` bytes.\n\
      * `buf` must be valid for reads and writes of 320 bytes; its contents on return are \
      unspecified.\n\
      * These three regions must not overlap each other, the stack frame of the call (the \
      return address and the arguments), or the 12 bytes of stack below the return address, \
      where its calls of `vg_chacha20_block` store their arguments and return address, and \
      none of them may wrap around the end of the address space (distinct Rust objects never \
      do)."
    code := Impl.ChaCha20.X86.Xor.xor
    contract := Spec.ChaCha20.xorContract X86.abi 12
    verified := Proof.ChaCha20.X86.Shared.xor }]

end VG.Artifacts.ChaCha20.X86

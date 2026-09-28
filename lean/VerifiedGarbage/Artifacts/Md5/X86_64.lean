import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Md5.X86_64.Shared

/-!
# MD5 (RFC 1321) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "md5"
    name := "vg_md5_compress"
    sig := Spec.Md5.compressSig
    doc := "The MD5 compression function (RFC 1321 §3.4): updates the MD buffer `*state` \
      (`A, B, C, D`) with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Md5.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the MD buffer or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 16 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 64 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Md5.X86_64.compress
    contract := Spec.Md5.compressContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.compress },
  { target := X86_64.target
    module := "md5"
    name := "vg_md5_init"
    sig := Spec.Md5.initSig
    doc := "Starts an MD5 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Md5.initContract`. The streaming state is the MD buffer followed \
      by a buffered partial block (`VG.Spec.Md5.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 80 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Md5.X86_64.Stream.init
    contract := Spec.Md5.initContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.init },
  { target := X86_64.target
    module := "md5"
    name := "vg_md5_update"
    sig := Spec.Md5.updateSig
    doc := "Absorbs data into an MD5 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Md5.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 80 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_md5_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Md5.X86_64.Stream.update
    contract := Spec.Md5.updateContract X86_64.abi 8
    verified := Proof.Md5.X86_64.Shared.update },
  { target := X86_64.target
    module := "md5"
    name := "vg_md5_finalize"
    sig := Spec.Md5.finalizeSig
    doc := "Finishes an MD5 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the MD5 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Md5.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 80 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 16 bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_md5_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Md5.X86_64.Stream.finalize
    contract := Spec.Md5.finalizeContract X86_64.abi 8
    verified := Proof.Md5.X86_64.Shared.finalize }]

end VG.Artifacts.Md5.X86_64

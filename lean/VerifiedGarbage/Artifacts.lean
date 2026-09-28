import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Proof.SpSafe
import VerifiedGarbage.Proof.Selftest.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.AArch64.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Shared
import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha1.AArch64.Shared
import VerifiedGarbage.Proof.Sha512.AArch64.Shared
import VerifiedGarbage.Proof.Sha512.Arm.Shared
import VerifiedGarbage.Proof.Hmac.X86_64.Shared
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Shared
import VerifiedGarbage.Proof.Md5.X86_64.Shared
import VerifiedGarbage.Proof.Md5.AArch64.Shared
import VerifiedGarbage.Proof.ChaCha20.X86_64.Shared
import VerifiedGarbage.Proof.ChaCha20.AArch64.Shared
import VerifiedGarbage.Proof.ChaCha20.Arm.Shared
import VerifiedGarbage.Proof.Sha256.X86.Shared
import VerifiedGarbage.Proof.Hmac.AArch64.Shared
import VerifiedGarbage.Proof.Hmac.Arm.Shared
import VerifiedGarbage.Proof.Hmac.X86.Shared
import VerifiedGarbage.Proof.ChaCha20.X86.Shared

/-!
# The artifact registry

**The single entry point.** Every function emitted into the Rust crate is an
entry of `artifacts`, and `Emit.lean` emits exactly this list. An
`Artifact` bundles

* the target and the Rust name and signature of the function,
* the implementation (`Impl/`),
* the contract it satisfies (`Spec/`), and
* the proof of `Verified` for them (`Proof/`),

so nothing can be emitted without a proof. The `#assert_standard_axioms`
check below then ensures none of those proofs relies on `sorry`,
`native_decide` or any axiom beyond Lean's standard three.

To add a function: write its spec and contract under `Spec/`, the code under
`Impl/`, the proof under `Proof/`, and append an entry here. Then run
`lake build && lake env lean --run Emit.lean` (in `lean/`) and commit the
regenerated `src/asm/`.

**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`.
-/

namespace VG

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "selftest"
    name := "vg_selftest_add"
    sig := Spec.Selftest.addSig
    doc := "Pipeline self-test: returns `a.wrapping_add(b)`.\n\n\
      Contract: `VG.Spec.Selftest.addContract`. No safety requirements."
    code := Impl.Selftest.X86_64.add
    contract := Spec.Selftest.addContract X86_64.abi
    verified := Proof.Selftest.X86_64.Shared.add
    spSafe := Proof.SpSafe.selftest_x86_64_add },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Spec.Sha256.compressSig
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress
    spSafe := Proof.SpSafe.sha256_x86_64_compress },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Spec.Sha256.initSig
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha256.X86_64.Stream.init
    contract := Spec.Sha256.initContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.init
    spSafe := Proof.SpSafe.sha256_x86_64_init },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Spec.Sha256.updateSig
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha256_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.update .scalar
    contract := Spec.Sha256.updateContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.update
    spSafe := Proof.SpSafe.sha256_x86_64_update },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Spec.Sha256.finalizeSig
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha256_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.finalize .scalar
    contract := Spec.Sha256.finalizeContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.finalize
    spSafe := Proof.SpSafe.sha256_x86_64_finalize },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_compress_shani"
    sig := Spec.Sha256.compressSig
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2), with the SHA extensions: \
      updates the hash value `*state` with the `n` 64-byte blocks starting at `blocks`, in \
      order.\n\n\
      Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.ShaNi.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress_shani
    spSafe := Proof.SpSafe.sha256_x86_64_compress_shani
    features := ["sha", "ssse3"] },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_update_shani"
    sig := Spec.Sha256.updateSig
    doc := "Absorbs data into a SHA-256 computation, with the SHA extensions: if the streaming \
      state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it then represents \
      that message followed by the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha256_compress_shani` stores \
      its return address (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.update .shani
    contract := Spec.Sha256.updateContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.update_shani
    spSafe := Proof.SpSafe.sha256_x86_64_update_shani
    features := ["sha", "ssse3"] },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_finalize_shani"
    sig := Spec.Sha256.finalizeSig
    doc := "Finishes a SHA-256 computation, with the SHA extensions: if the streaming state \
      `*state` represents a message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest \
      of that message to `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha256_compress_shani` stores \
      its return address (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.finalize .shani
    contract := Spec.Sha256.finalizeContract X86_64.abi 8
    verified := Proof.Sha256.X86_64.Shared.finalize_shani
    spSafe := Proof.SpSafe.sha256_x86_64_finalize_shani
    features := ["sha", "ssse3"] },
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
    verified := Proof.Md5.X86_64.Shared.compress
    spSafe := Proof.SpSafe.md5_x86_64_compress },
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
    verified := Proof.Md5.X86_64.Shared.init
    spSafe := Proof.SpSafe.md5_x86_64_init },
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
    verified := Proof.Md5.X86_64.Shared.update
    spSafe := Proof.SpSafe.md5_x86_64_update },
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
    verified := Proof.Md5.X86_64.Shared.finalize
    spSafe := Proof.SpSafe.md5_x86_64_finalize },
  { target := AArch64.target
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
      * These three regions must not overlap each other."
    code := Impl.Md5.AArch64.compress
    contract := Spec.Md5.compressContract AArch64.abi
    verified := Proof.Md5.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "md5"
    name := "vg_md5_init"
    sig := Spec.Md5.initSig
    doc := "Starts an MD5 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Md5.initContract`. The streaming state is the MD buffer followed \
      by a buffered partial block (`VG.Spec.Md5.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 80 bytes."
    code := Impl.Md5.AArch64.Stream.init
    contract := Spec.Md5.initContract AArch64.abi
    verified := Proof.Md5.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
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
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address before calling `vg_md5_compress` \
      (distinct Rust objects never do)."
    code := Impl.Md5.AArch64.Stream.update
    contract := Spec.Md5.updateContract AArch64.abi 16
    verified := Proof.Md5.AArch64.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
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
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address before calling `vg_md5_compress` \
      (distinct Rust objects never do)."
    code := Impl.Md5.AArch64.Stream.finalize
    contract := Spec.Md5.finalizeContract AArch64.abi 16
    verified := Proof.Md5.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := X86_64.target
    module := "sha1"
    name := "vg_sha1_compress"
    sig := Spec.Sha1.compressSig
    doc := "The SHA-1 compression function (FIPS 180-4 §6.1.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha1.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 20 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha1.X86_64.compress
    contract := Spec.Sha1.compressContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.compress
    spSafe := Proof.SpSafe.sha1_x86_64_compress },
  { target := X86_64.target
    module := "sha1"
    name := "vg_sha1_init"
    sig := Spec.Sha1.initSig
    doc := "Starts a SHA-1 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha1.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha1.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 84 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha1.X86_64.Stream.init
    contract := Spec.Sha1.initContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.init
    spSafe := Proof.SpSafe.sha1_x86_64_init },
  { target := X86_64.target
    module := "sha1"
    name := "vg_sha1_update"
    sig := Spec.Sha1.updateSig
    doc := "Absorbs data into a SHA-1 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha1.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 84 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha1_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha1.X86_64.Stream.update
    contract := Spec.Sha1.updateContract X86_64.abi 8
    verified := Proof.Sha1.X86_64.Shared.update
    spSafe := Proof.SpSafe.sha1_x86_64_update },
  { target := X86_64.target
    module := "sha1"
    name := "vg_sha1_finalize"
    sig := Spec.Sha1.finalizeSig
    doc := "Finishes a SHA-1 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-1 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha1.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 84 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 20 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha1_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha1.X86_64.Stream.finalize
    contract := Spec.Sha1.finalizeContract X86_64.abi 8
    verified := Proof.Sha1.X86_64.Shared.finalize
    spSafe := Proof.SpSafe.sha1_x86_64_finalize },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_compress"
    sig := Spec.Sha512.compressSig
    doc := "The SHA-512 compression function (FIPS 180-4 §6.4.2), shared by SHA-384, SHA-512, \
      SHA-512/224 and SHA-512/256: updates the hash value `*state` with the `n` 128-byte \
      blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha512.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes.\n\
      * `blocks` must be valid for reads of `128 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 224 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha512.X86_64.compress
    contract := Spec.Sha512.compressContract X86_64.abi
    verified := Proof.Sha512.X86_64.Shared.compress
    spSafe := Proof.SpSafe.sha512_x86_64_compress },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha384_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-384 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-384 (`VG.Spec.Sha512.H0_384`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_384`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_384
    spSafe := Proof.SpSafe.sha512_x86_64_init_h0_384 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512 (`VG.Spec.Sha512.H0_512`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512
    spSafe := Proof.SpSafe.sha512_x86_64_init_h0_512 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_224_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/224 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/224 (`VG.Spec.Sha512.H0_512_224`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_224`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_224
    spSafe := Proof.SpSafe.sha512_x86_64_init_h0_512_224 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_256_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/256 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/256 (`VG.Spec.Sha512.H0_512_256`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_256`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_256
    spSafe := Proof.SpSafe.sha512_x86_64_init_h0_512_256 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_update"
    sig := Spec.Sha512.updateSig
    doc := "Absorbs data into a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if \
      the streaming state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it \
      then represents that message followed by the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha512.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 192 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha512_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha512.X86_64.Stream.update
    contract := Spec.Sha512.updateContract X86_64.abi 8
    verified := Proof.Sha512.X86_64.Shared.update
    spSafe := Proof.SpSafe.sha512_x86_64_update },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_finalize"
    sig := Spec.Sha512.finalizeSig
    doc := "Finishes a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
      streaming state `*state` represents a message of `count` bytes, hashed from an initial \
      hash value, writes the final hash value `H⁽ᴺ⁾` of that message (64 bytes) to `*out`. \
      The SHA-512 digest is all of it; the SHA-384, SHA-512/224 and SHA-512/256 digests are \
      its first 48, 28 and 32 bytes.\n\n\
      Contract: `VG.Spec.Sha512.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are \
      not supported.\n\
      * `state` must be valid for reads and writes of 192 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 64 bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_sha512_compress` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha512.X86_64.Stream.finalize
    contract := Spec.Sha512.finalizeContract X86_64.abi 8
    verified := Proof.Sha512.X86_64.Shared.finalize
    spSafe := Proof.SpSafe.sha512_x86_64_finalize },
  { target := X86_64.target
    module := "hmac"
    name := "vg_hmac_sha256_init"
    sig := Spec.Hmac.initSha256Sig
    doc := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the \
      SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent \
      `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes \
      (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its \
      `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.\n\n\
      Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and \
      `key_len` may affect timing, not the key.\n\n\
      # Safety\n\n\
      * `key_len` must be at most 64.\n\
      * `inner` and `outer` must each be valid for reads and writes of 96 bytes.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These four regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its calls of `vg_sha256_compress` store their \
      return address (distinct Rust objects never do)."
    code := Impl.Hmac.X86_64.init
    contract := Spec.Hmac.initSha256Contract X86_64.abi 8
    verified := Proof.Hmac.X86_64.Shared.init
    spSafe := Proof.SpSafe.hmac_x86_64_init },
  { target := X86_64.target
    module := "hmac"
    name := "vg_hmac_sha256_finalize"
    sig := Spec.Hmac.finalizeSha256Sig
    doc := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
      SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes \
      (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the \
      text under `K₀` in bytes 176 to 207 of `*scratch`.\n\n\
      Contract: `VG.Spec.Hmac.finalizeSha256Contract`. Constant time: only the pointers and \
      `count` may affect timing, not the states.\n\n\
      # Safety\n\n\
      * `inner` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `outer` must be valid for reads of 96 bytes.\n\
      * `scratch` must be valid for reads and writes of 240 bytes; its contents on return \
      are unspecified, apart from the MAC.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 16 bytes of stack below it, where its calls of `vg_sha256_finalize` (which \
      calls `vg_sha256_compress`) store their return addresses (distinct Rust objects never \
      do)."
    code := Impl.Hmac.X86_64.finalize
    contract := Spec.Hmac.finalizeSha256Contract X86_64.abi 16
    verified := Proof.Hmac.X86_64.Shared.finalize
    spSafe := Proof.SpSafe.hmac_x86_64_finalize },
  { target := X86_64.target
    module := "pbkdf2"
    name := "vg_pbkdf2_hmac_sha256_iterate"
    sig := Spec.Pbkdf2.iterateSha256Sig
    doc := "Runs `n` steps of PBKDF2-HMAC-SHA-256's iteration: if, for a 64-byte key `K₀`, the \
      SHA-256 streaming state in bytes 0 to 95 of `*key` represents `K₀ ⊕ ipad` and the one \
      in bytes 96 to 191 represents `K₀ ⊕ opad` (as `vg_hmac_sha256_init` leaves them), \
      repeats `U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u` and `T = *t`, \
      and leaves the final `T` in `*t` (RFC 8018, step 3 of `F`).\n\n\
      Contract: `VG.Spec.Pbkdf2.iterateSha256Contract`. Constant time: only the pointers and \
      `n` may affect timing, not the key, `U` or `T`.\n\n\
      # Safety\n\n\
      * `key` must be valid for reads of 192 bytes, and `u` for reads of 32 bytes.\n\
      * `t` must be valid for reads and writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 384 bytes; its contents on return \
      are unspecified.\n\
      * `t` and `scratch` must not overlap each other, `key` or `u`, and none of the four \
      regions may overlap the return address on the stack or the 8 bytes of stack below it, \
      where its calls of `vg_sha256_compress` store their return address (distinct Rust \
      objects never do)."
    code := Impl.Pbkdf2.X86_64.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8
    verified := Proof.Pbkdf2.X86_64.Shared.iterate
    spSafe := Proof.SpSafe.pbkdf2_x86_64_iterate },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Spec.Sha256.compressSig
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha256.AArch64.compress
    contract := Spec.Sha256.compressContract AArch64.abi
    verified := Proof.Sha256.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Spec.Sha256.initSig
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes."
    code := Impl.Sha256.AArch64.Stream.init
    contract := Spec.Sha256.initContract AArch64.abi
    verified := Proof.Sha256.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Spec.Sha256.updateSig
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address (distinct Rust objects never do)."
    code := Impl.Sha256.AArch64.Stream.update
    contract := Spec.Sha256.updateContract AArch64.abi 16
    verified := Proof.Sha256.AArch64.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Spec.Sha256.finalizeSig
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and \
      `count` may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address (distinct Rust objects never do)."
    code := Impl.Sha256.AArch64.Stream.finalize
    contract := Spec.Sha256.finalizeContract AArch64.abi 16
    verified := Proof.Sha256.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_compress"
    sig := Spec.Sha1.compressSig
    doc := "The SHA-1 compression function (FIPS 180-4 §6.1.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha1.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 20 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha1.AArch64.compress
    contract := Spec.Sha1.compressContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_init"
    sig := Spec.Sha1.initSig
    doc := "Starts a SHA-1 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha1.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha1.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 84 bytes."
    code := Impl.Sha1.AArch64.Stream.init
    contract := Spec.Sha1.initContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_update"
    sig := Spec.Sha1.updateSig
    doc := "Absorbs data into a SHA-1 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha1.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 84 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address around its calls of \
      `vg_sha1_compress` (distinct Rust objects never do)."
    code := Impl.Sha1.AArch64.Stream.update
    contract := Spec.Sha1.updateContract AArch64.abi 16
    verified := Proof.Sha1.AArch64.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha1"
    name := "vg_sha1_finalize"
    sig := Spec.Sha1.finalizeSig
    doc := "Finishes a SHA-1 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-1 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha1.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 84 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 20 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address around its calls of \
      `vg_sha1_compress` (distinct Rust objects never do)."
    code := Impl.Sha1.AArch64.Stream.finalize
    contract := Spec.Sha1.finalizeContract AArch64.abi 16
    verified := Proof.Sha1.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "sha512"
    name := "vg_sha512_compress"
    sig := Spec.Sha512.compressSig
    doc := "The SHA-512 compression function (FIPS 180-4 §6.4.2), shared by SHA-384, SHA-512, \
      SHA-512/224 and SHA-512/256: updates the hash value `*state` with the `n` 128-byte \
      blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha512.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes.\n\
      * `blocks` must be valid for reads of `128 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 224 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha512.AArch64.compress
    contract := Spec.Sha512.compressContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.compress },
  { target := AArch64.target
    module := "sha512"
    name := "vg_sha384_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-384 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-384 (`VG.Spec.Sha512.H0_384`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_384`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes."
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_384 },
  { target := AArch64.target
    module := "sha512"
    name := "vg_sha512_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512 (`VG.Spec.Sha512.H0_512`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes."
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512 },
  { target := AArch64.target
    module := "sha512"
    name := "vg_sha512_224_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/224 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/224 (`VG.Spec.Sha512.H0_512_224`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_224`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes."
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_224 },
  { target := AArch64.target
    module := "sha512"
    name := "vg_sha512_256_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/256 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/256 (`VG.Spec.Sha512.H0_512_256`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_256`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes."
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_256 },
  { target := AArch64.target
    module := "sha512"
    name := "vg_sha512_update"
    sig := Spec.Sha512.updateSig
    doc := "Absorbs data into a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if \
      the streaming state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it \
      then represents that message followed by the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha512.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 192 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha512.AArch64.Stream.update
    contract := Spec.Sha512.updateContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.update },
  { target := AArch64.target
    module := "sha512"
    name := "vg_sha512_finalize"
    sig := Spec.Sha512.finalizeSig
    doc := "Finishes a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
      streaming state `*state` represents a message of `count` bytes, hashed from an initial \
      hash value, writes the final hash value `H⁽ᴺ⁾` of that message (64 bytes) to `*out`. \
      The SHA-512 digest is all of it; the SHA-384, SHA-512/224 and SHA-512/256 digests are \
      its first 48, 28 and 32 bytes.\n\n\
      Contract: `VG.Spec.Sha512.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are \
      not supported.\n\
      * `state` must be valid for reads and writes of 192 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 64 bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha512.AArch64.Stream.finalize
    contract := Spec.Sha512.finalizeContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.finalize },
  { target := AArch64.target
    module := "hmac"
    name := "vg_hmac_sha256_init"
    sig := Spec.Hmac.initSha256Sig
    doc := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the \
      SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent \
      `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes \
      (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its \
      `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.\n\n\
      Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and \
      `key_len` may affect timing, not the key.\n\n\
      # Safety\n\n\
      * `key_len` must be at most 64.\n\
      * `inner` and `outer` must each be valid for reads and writes of 96 bytes.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These four regions must not overlap each other, or the 16 bytes of stack below the \
      stack pointer, where it saves its return address (distinct Rust objects never do)."
    code := Impl.Hmac.AArch64.init
    contract := Spec.Hmac.initSha256Contract AArch64.abi 16
    verified := Proof.Hmac.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "hmac"
    name := "vg_hmac_sha256_finalize"
    sig := Spec.Hmac.finalizeSha256Sig
    doc := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
      SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes \
      (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the \
      text under `K₀` in bytes 176 to 207 of `*scratch`.\n\n\
      Contract: `VG.Spec.Hmac.finalizeSha256Contract`. Constant time: only the pointers and \
      `count` may affect timing, not the states.\n\n\
      # Safety\n\n\
      * `inner` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `outer` must be valid for reads of 96 bytes.\n\
      * `scratch` must be valid for reads and writes of 240 bytes; its contents on return \
      are unspecified, apart from the MAC.\n\
      * These three regions must not overlap each other, or the 32 bytes of stack below the \
      stack pointer, where it and its calls of `vg_sha256_finalize` save their return \
      addresses (distinct Rust objects never do)."
    code := Impl.Hmac.AArch64.finalize
    contract := Spec.Hmac.finalizeSha256Contract AArch64.abi 32
    verified := Proof.Hmac.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Spec.Sha256.compressSig
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, and none of them may wrap \
      around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.compress
    contract := Spec.Sha256.compressContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Spec.Sha256.initSig
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.Stream.init
    contract := Spec.Sha256.initContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Spec.Sha256.updateSig
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha256.Arm.Stream.update
    contract := Spec.Sha256.updateContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Spec.Sha256.finalizeSig
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha256.Arm.Stream.finalize
    contract := Spec.Sha256.finalizeContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_compress"
    sig := Spec.Sha512.compressSig
    doc := "The SHA-512 compression function (FIPS 180-4 §6.4.2), shared by SHA-384, SHA-512, \
      SHA-512/224 and SHA-512/256: updates the hash value `*state` with the `n` 128-byte \
      blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha512.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes.\n\
      * `blocks` must be valid for reads of `128 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 224 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, and none of them may wrap \
      around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.compress
    contract := Spec.Sha512.compressContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha384_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-384 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-384 (`VG.Spec.Sha512.H0_384`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_384`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512 (`VG.Spec.Sha512.H0_512`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_224_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/224 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/224 (`VG.Spec.Sha512.H0_512_224`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_224`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_256_init"
    sig := Spec.Sha512.initSig
    doc := "Starts a SHA-512/256 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/256 (`VG.Spec.Sha512.H0_512_256`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_256`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256 },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_update"
    sig := Spec.Sha512.updateSig
    doc := "Absorbs data into a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if \
      the streaming state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it \
      then represents that message followed by the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha512.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 192 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha512.Arm.Stream.update
    contract := Spec.Sha512.updateContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "sha512"
    name := "vg_sha512_finalize"
    sig := Spec.Sha512.finalizeSig
    doc := "Finishes a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
      streaming state `*state` represents a message of `count` bytes, hashed from an initial \
      hash value, writes the final hash value `H⁽ᴺ⁾` of that message (64 bytes) to `*out`. \
      The SHA-512 digest is all of it; the SHA-384, SHA-512/224 and SHA-512/256 digests are \
      its first 48, 28 and 32 bytes.\n\n\
      Contract: `VG.Spec.Sha512.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are \
      not supported.\n\
      * `state` must be valid for reads and writes of 192 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 64 bytes.\n\
      * `scratch` must be valid for reads and writes of 272 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha512.Arm.Stream.finalize
    contract := Spec.Sha512.finalizeContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := X86_64.target
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
      * `buf` must not overlap `state`, nor the return address on the stack (distinct Rust \
      objects never do)."
    code := Impl.ChaCha20.X86_64.block
    contract := Spec.ChaCha20.blockContract X86_64.abi
    verified := Proof.ChaCha20.X86_64.Shared.block
    spSafe := Proof.SpSafe.chacha20_x86_64_block },
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
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
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
      * `buf` must not overlap `state`, and neither may wrap around the end of the address \
      space (no Rust object does)."
    code := Impl.ChaCha20.Arm.block
    contract := Spec.ChaCha20.blockContract Arm.abi
    verified := Proof.ChaCha20.Arm.Shared.block
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := X86.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Spec.Sha256.compressSig
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other or the stack frame of the \
      call (the return address and the arguments), and none of them may wrap around \
      the end of the address space (no Rust object does)."
    code := Impl.Sha256.X86.compress
    contract := Spec.Sha256.compressContract X86.abi
    verified := Proof.Sha256.X86.Shared.compress
    spSafe := Proof.SpSafe.sha256_x86_compress },
  { target := X86.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Spec.Sha256.initSig
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not overlap the stack frame of the call (the return address and the \
      argument), and must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha256.X86.Stream.init
    contract := Spec.Sha256.initContract X86.abi
    verified := Proof.Sha256.X86.Shared.init
    spSafe := Proof.SpSafe.sha256_x86_init },
  { target := X86.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Spec.Sha256.updateSig
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data. The function overwrites its own \
      arguments on the stack (which the callee owns under cdecl).\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other or the stack frame of the call \
      (the return address and the arguments), and none of them may wrap around the end of \
      the address space (distinct Rust objects never do)."
    code := Impl.Sha256.X86.Stream.update
    contract := Spec.Sha256.updateContract X86.abi
    verified := Proof.Sha256.X86.Shared.update
    spSafe := Proof.SpSafe.sha256_x86_update },
  { target := X86.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Spec.Sha256.finalizeSig
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` \
      may affect timing, not the state. The function overwrites its own arguments on the \
      stack (which the callee owns under cdecl).\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other or the stack frame of the call \
      (the return address and the arguments), and none of them may wrap around the end of \
      the address space (distinct Rust objects never do)."
    code := Impl.Sha256.X86.Stream.finalize
    contract := Spec.Sha256.finalizeContract X86.abi
    verified := Proof.Sha256.X86.Shared.finalize
    spSafe := Proof.SpSafe.sha256_x86_finalize },
  { target := Arm.target
    module := "hmac"
    name := "vg_hmac_sha256_init"
    sig := Spec.Hmac.initSha256Sig
    doc := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the \
      SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent \
      `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes \
      (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its \
      `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.\n\n\
      Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and \
      `key_len` may affect timing, not the key.\n\n\
      # Safety\n\n\
      * `key_len` must be at most 64.\n\
      * `inner` and `outer` must each be valid for reads and writes of 96 bytes.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These four regions must not overlap each other, and `inner`, `outer` and \
      `scratch` must not overlap the call's stack argument; none of them may wrap around \
      the end of the address space (distinct Rust objects never do)."
    code := Impl.Hmac.Arm.init
    contract := Spec.Hmac.initSha256Contract Arm.abi
    verified := Proof.Hmac.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := Arm.target
    module := "hmac"
    name := "vg_hmac_sha256_finalize"
    sig := Spec.Hmac.finalizeSha256OutSig
    doc := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
      SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes \
      (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the \
      text under `K₀` to `*out`.\n\n\
      Contract: `VG.Spec.Hmac.finalizeSha256OutContract`. Constant time: only the pointers and \
      `count` may affect timing, not the states.\n\n\
      # Safety\n\n\
      * `inner` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `outer` must be valid for reads of 96 bytes.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 240 bytes; its contents on return \
      are unspecified.\n\
      * `inner`, `out` and `scratch` must not overlap each other, `outer` or the call's \
      stack arguments, and none of the four may wrap around the end of the address space \
      (distinct Rust objects never do)."
    code := Impl.Hmac.Arm.finalize
    contract := Spec.Hmac.finalizeSha256OutContract Arm.abi
    verified := Proof.Hmac.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := X86.target
    module := "hmac"
    name := "vg_hmac_sha256_init"
    sig := Spec.Hmac.initSha256Sig
    doc := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the \
      SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent \
      `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes \
      (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its \
      `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.\n\n\
      Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and \
      `key_len` may affect timing, not the key. The function overwrites its own arguments \
      on the stack (which the callee owns under cdecl).\n\n\
      # Safety\n\n\
      * `key_len` must be at most 64.\n\
      * `inner` and `outer` must each be valid for reads and writes of 96 bytes.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These four regions must not overlap each other or the arguments of the call, \
      `inner`, `outer` and `scratch` must not overlap its return address, and none of \
      them may wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.Hmac.X86.init
    contract := Spec.Hmac.initSha256Contract X86.abi
    verified := Proof.Hmac.X86.Shared.init
    spSafe := Proof.SpSafe.hmac_x86_init },
  { target := X86.target
    module := "hmac"
    name := "vg_hmac_sha256_finalize"
    sig := Spec.Hmac.finalizeSha256OutSig
    doc := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
      SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes \
      (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the \
      text under `K₀` to `*out`.\n\n\
      Contract: `VG.Spec.Hmac.finalizeSha256OutContract`. Constant time: only the pointers and \
      `count` may affect timing, not the states. The function overwrites its own \
      arguments on the stack (which the callee owns under cdecl).\n\n\
      # Safety\n\n\
      * `inner` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `outer` must be valid for reads of 96 bytes.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 240 bytes; its contents on return \
      are unspecified.\n\
      * `inner`, `out` and `scratch` must not overlap each other, `outer` or the stack \
      frame of the call (the return address and the arguments); `outer` must not overlap \
      the arguments; and none of the four may wrap around the end of the address space \
      (distinct Rust objects never do)."
    code := Impl.Hmac.X86.finalize
    contract := Spec.Hmac.finalizeSha256OutContract X86.abi
    verified := Proof.Hmac.X86.Shared.finalize
    spSafe := Proof.SpSafe.hmac_x86_finalize },
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
    verified := Proof.ChaCha20.X86.Shared.block
    spSafe := Proof.SpSafe.chacha20_x86_block }
]

#assert_standard_axioms artifacts

end VG

import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Proof.Selftest.X86_64
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Finalize
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Update
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Finalize
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Update
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.X86_64.Init
import VerifiedGarbage.Proof.Hmac.X86_64.Finalize
import VerifiedGarbage.Proof.ChaCha20.X86_64.Block
import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Proof.ChaCha20.Arm.Block

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

/-! ## Signatures

The Rust signatures of the artifacts (rendered by `Sig.rust`). -/

namespace Sigs

def selftestAdd : Sig where
  params := [("a", .int .u64 false), ("b", .int .u64 false)]
  ret := some .u64

def sha256Compress : Sig where
  params := [("state", .array true .u32 8), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 14)]

def sha256Init : Sig where
  params := [("state", .array true .u8 96)]

def sha256Update : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 20)]

def sha256Finalize : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32), ("scratch", .array true .u64 20)]

def sha512Compress : Sig where
  params := [("state", .array true .u64 8), ("blocks", .slice false (.array .u8 128) "n"),
    ("scratch", .array true .u64 22)]

def sha512Init : Sig where
  params := [("state", .array true .u8 192)]

def sha512Update : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 28)]

def sha512Finalize : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64), ("scratch", .array true .u64 28)]

def hmacSha256Init : Sig where
  params := [("inner", .array true .u8 96), ("outer", .array true .u8 96),
    ("key", .slice false .u8 "key_len"), ("scratch", .array true .u64 20)]

def hmacSha256Finalize : Sig where
  params := [("inner", .array true .u8 96), ("outer", .array false .u8 96),
    ("count", .int .u64 true), ("scratch", .array true .u64 30)]

def chacha20Block : Sig where
  params := [("state", .array false .u32 16), ("buf", .array true .u32 64)]

end Sigs

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "selftest"
    name := "vg_selftest_add"
    sig := Sigs.selftestAdd
    doc := "Pipeline self-test: returns `a.wrapping_add(b)`.\n\n\
      Contract: `VG.Spec.Selftest.addX86_64`. No safety requirements."
    code := Impl.Selftest.X86_64.add
    contract := Spec.Selftest.addX86_64
    verified := Proof.Selftest.X86_64.add_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Sigs.sha256Compress
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressX86_64`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.compress
    contract := Spec.Sha256.compressX86_64
    verified := Proof.Sha256.X86_64.compress_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Sigs.sha256Init
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initX86_64`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha256.X86_64.Stream.init
    contract := Spec.Sha256.initX86_64
    verified := Proof.Sha256.X86_64.Stream.init_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Sigs.sha256Update
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateX86_64`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.update
    contract := Spec.Sha256.updateX86_64
    verified := Proof.Sha256.X86_64.Stream.Update.update_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Sigs.sha256Finalize
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeX86_64`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.finalize
    contract := Spec.Sha256.finalizeX86_64
    verified := Proof.Sha256.X86_64.Stream.Finalize.finalize_verified },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_compress"
    sig := Sigs.sha512Compress
    doc := "The SHA-512 compression function (FIPS 180-4 §6.4.2), shared by SHA-384, SHA-512, \
      SHA-512/224 and SHA-512/256: updates the hash value `*state` with the `n` 128-byte \
      blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha512.compressX86_64`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes.\n\
      * `blocks` must be valid for reads of `128 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 176 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha512.X86_64.compress
    contract := Spec.Sha512.compressX86_64
    verified := Proof.Sha512.X86_64.compress_verified },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha384_init"
    sig := Sigs.sha512Init
    doc := "Starts a SHA-384 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-384 (`VG.Spec.Sha512.H0_384`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initX86_64 VG.Spec.Sha512.H0_384`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initX86_64 Spec.Sha512.H0_384
    verified := Proof.Sha512.X86_64.Stream.init_verified Spec.Sha512.H0_384 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_init"
    sig := Sigs.sha512Init
    doc := "Starts a SHA-512 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512 (`VG.Spec.Sha512.H0_512`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initX86_64 VG.Spec.Sha512.H0_512`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initX86_64 Spec.Sha512.H0_512
    verified := Proof.Sha512.X86_64.Stream.init_verified Spec.Sha512.H0_512 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_224_init"
    sig := Sigs.sha512Init
    doc := "Starts a SHA-512/224 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/224 (`VG.Spec.Sha512.H0_512_224`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initX86_64 VG.Spec.Sha512.H0_512_224`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initX86_64 Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86_64.Stream.init_verified Spec.Sha512.H0_512_224 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_256_init"
    sig := Sigs.sha512Init
    doc := "Starts a SHA-512/256 computation: makes the SHA-512 streaming state `*state` represent \
      the empty message, hashed from the initial hash value of SHA-512/256 (`VG.Spec.Sha512.H0_512_256`). \
      Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
      Contract: `VG.Spec.Sha512.initX86_64 VG.Spec.Sha512.H0_512_256`. The streaming state is the \
      hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 192 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initX86_64 Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86_64.Stream.init_verified Spec.Sha512.H0_512_256 },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_update"
    sig := Sigs.sha512Update
    doc := "Absorbs data into a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if \
      the streaming state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it \
      then represents that message followed by the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha512.updateX86_64`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 192 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 224 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha512.X86_64.Stream.update
    contract := Spec.Sha512.updateX86_64
    verified := Proof.Sha512.X86_64.Stream.Update.update_verified },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_finalize"
    sig := Sigs.sha512Finalize
    doc := "Finishes a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
      streaming state `*state` represents a message of `count` bytes, hashed from an initial \
      hash value, writes the final hash value `H⁽ᴺ⁾` of that message (64 bytes) to `*out`. \
      The SHA-512 digest is all of it; the SHA-384, SHA-512/224 and SHA-512/256 digests are \
      its first 48, 28 and 32 bytes.\n\n\
      Contract: `VG.Spec.Sha512.finalizeX86_64`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are \
      not supported.\n\
      * `state` must be valid for reads and writes of 192 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 64 bytes.\n\
      * `scratch` must be valid for reads and writes of 224 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha512.X86_64.Stream.finalize
    contract := Spec.Sha512.finalizeX86_64
    verified := Proof.Sha512.X86_64.Stream.Finalize.finalize_verified },
  { target := X86_64.target
    module := "hmac"
    name := "vg_hmac_sha256_init"
    sig := Sigs.hmacSha256Init
    doc := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the \
      SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent \
      `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes \
      (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its \
      `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.\n\n\
      Contract: `VG.Spec.Hmac.initSha256X86_64`. Constant time: only the pointers and \
      `key_len` may affect timing, not the key.\n\n\
      # Safety\n\n\
      * `key_len` must be at most 64.\n\
      * `inner` and `outer` must each be valid for reads and writes of 96 bytes.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These four regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Hmac.X86_64.init
    contract := Spec.Hmac.initSha256X86_64
    verified := Proof.Hmac.X86_64.Init.init_verified },
  { target := X86_64.target
    module := "hmac"
    name := "vg_hmac_sha256_finalize"
    sig := Sigs.hmacSha256Finalize
    doc := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
      SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes \
      (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the \
      text under `K₀` in bytes 176 to 207 of `*scratch`.\n\n\
      Contract: `VG.Spec.Hmac.finalizeSha256X86_64`. Constant time: only the pointers and \
      `count` may affect timing, not the states.\n\n\
      # Safety\n\n\
      * `inner` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `outer` must be valid for reads of 96 bytes.\n\
      * `scratch` must be valid for reads and writes of 240 bytes; its contents on return \
      are unspecified, apart from the MAC.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Hmac.X86_64.finalize
    contract := Spec.Hmac.finalizeSha256X86_64
    verified := Proof.Hmac.X86_64.Finalize.finalize_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Sigs.sha256Compress
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressAArch64`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha256.AArch64.compress
    contract := Spec.Sha256.compressAArch64
    verified := Proof.Sha256.AArch64.compress_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Sigs.sha256Init
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initAArch64`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes."
    code := Impl.Sha256.AArch64.Stream.init
    contract := Spec.Sha256.initAArch64
    verified := Proof.Sha256.AArch64.Stream.init_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Sigs.sha256Update
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateAArch64`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha256.AArch64.Stream.update
    contract := Spec.Sha256.updateAArch64
    verified := Proof.Sha256.AArch64.Stream.Update.update_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Sigs.sha256Finalize
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeAArch64`. Constant time: only the pointers and \
      `count` may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha256.AArch64.Stream.finalize
    contract := Spec.Sha256.finalizeAArch64
    verified := Proof.Sha256.AArch64.Stream.Finalize.finalize_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_compress"
    sig := Sigs.sha256Compress
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressArm`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, and none of them may wrap \
      around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.compress
    contract := Spec.Sha256.compressArm
    verified := Proof.Sha256.Arm.compress_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_init"
    sig := Sigs.sha256Init
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initArm`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.Stream.init
    contract := Spec.Sha256.initArm
    verified := Proof.Sha256.Arm.Stream.init_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_update"
    sig := Sigs.sha256Update
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateArm`. Constant time: only the pointers, `count` and \
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
    contract := Spec.Sha256.updateArm
    verified := Proof.Sha256.Arm.Stream.Update.update_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_finalize"
    sig := Sigs.sha256Finalize
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeArm`. Constant time: only the pointers and `count` \
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
    contract := Spec.Sha256.finalizeArm
    verified := Proof.Sha256.Arm.Stream.Finalize.finalize_verified },
  { target := X86_64.target
    module := "chacha20"
    name := "vg_chacha20_block"
    sig := Sigs.chacha20Block
    doc := "The ChaCha20 block function (RFC 8439 §2.3): writes the block function of the \
      16-word state `*state` (20 rounds, then the input state added word by word) to the \
      first 16 words of `*buf`.\n\n\
      Contract: `VG.Spec.ChaCha20.blockX86_64`. Constant time: only the pointers may affect \
      timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads of 64 bytes.\n\
      * `buf` must be valid for reads and writes of 256 bytes. On return its first 64 bytes \
      hold the result and the rest is unspecified.\n\
      * `buf` must not overlap `state`, nor the return address on the stack (distinct Rust \
      objects never do)."
    code := Impl.ChaCha20.X86_64.block
    contract := Spec.ChaCha20.blockX86_64
    verified := Proof.ChaCha20.X86_64.block_verified },
  { target := AArch64.target
    module := "chacha20"
    name := "vg_chacha20_block"
    sig := Sigs.chacha20Block
    doc := "The ChaCha20 block function (RFC 8439 §2.3): writes the block function of the \
      16-word state `*state` (20 rounds, then the input state added word by word) to the \
      first 16 words of `*buf`.\n\n\
      Contract: `VG.Spec.ChaCha20.blockAArch64`. Constant time: only the pointers may affect \
      timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads of 64 bytes.\n\
      * `buf` must be valid for reads and writes of 256 bytes. On return its first 64 bytes \
      hold the result and the rest is unspecified.\n\
      * `buf` must not overlap `state`."
    code := Impl.ChaCha20.AArch64.block
    contract := Spec.ChaCha20.blockAArch64
    verified := Proof.ChaCha20.AArch64.block_verified },
  { target := Arm.target
    module := "chacha20"
    name := "vg_chacha20_block"
    sig := Sigs.chacha20Block
    doc := "The ChaCha20 block function (RFC 8439 §2.3): writes the block function of the \
      16-word state `*state` (20 rounds, then the input state added word by word) to the \
      first 16 words of `*buf`.\n\n\
      Contract: `VG.Spec.ChaCha20.blockArm`. Constant time: only the pointers may affect \
      timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads of 64 bytes.\n\
      * `buf` must be valid for reads and writes of 256 bytes. On return its first 64 bytes \
      hold the result and the rest is unspecified.\n\
      * `buf` must not overlap `state`, and neither may wrap around the end of the address \
      space (no Rust object does)."
    code := Impl.ChaCha20.Arm.block
    contract := Spec.ChaCha20.blockArm
    verified := Proof.ChaCha20.Arm.block_verified }
]

#assert_standard_axioms artifacts

end VG

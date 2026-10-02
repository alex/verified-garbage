import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.Artifact

/-!
# HMAC-SHA-256: the contracts, on the 32-bit targets

**Trusted** (as every file in `Spec/`). An HMAC-SHA-256 computation is two
SHA-256 streaming states (`VG.Spec.Sha256.Repr`): the inner one, which
absorbs `(K₀ ⊕ ipad) ‖ text`, and the outer one, which holds `K₀ ⊕ opad`.
`vg_hmac_sha256_init` sets them up from the key, the text is absorbed into
the inner state with `vg_sha256_update` (`VG.Spec.Sha256.updateContract`),
and `vg_hmac_sha256_finalize` computes the MAC.

`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the rest. `vg_hmac_sha256_init` and `vg_hmac_sha256_finalize` may overwrite
their arguments passed in memory, where the calling convention allows it
(`writeArgs`), to pass arguments to the code they inline.
`vg_hmac_sha256_finalize` writes the MAC through an `out` pointer
(`finalizeSha256OutContract`), so that its arguments are those of
`vg_sha256_finalize` with `outer` inserted after `inner`.

These contracts are SHA-256's alone, for its implementations on the 32-bit
targets: `VG.Spec.Hmac.sha256I`'s generic ones (`Spec/Hmac/Generic.lean`),
as every hash function's, give the functions more working space. The 64-bit
targets implement SHA-256 through `sha256I` already; these are removed once
the 32-bit ones do too.

`init` and `finalize` take the number of bytes of stack below the stack pointer that
an implementation's calls use (`stack`, see `Sig.contract`), 0 for one that
makes no call: it depends on the target, and on which functions the
implementation calls.
-/

namespace VG.Spec.Hmac

open Sha256 (Repr bytesAt)

/-- `vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 76])`.
`scratch` is working space. -/
def initSha256Sig : Sig where
  params := [("inner", .array true .u8 96), ("outer", .array true .u8 96),
    ("key", .slice false .u8 "key_len"), ("scratch", .array true .u64 76)]

/-- For a key of at most 64 bytes (the SHA-256 block size): makes the
streaming state at `inner` represent `K₀ ⊕ ipad` and the one at `outer`
represent `K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.
The key is secret. -/
def initSha256Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSha256Sig.contract A
    (pre := fun _inner _outer _key keyLen _scratch _ => keyLen.toNat ≤ 64)
    (post := fun inner outer key keyLen _scratch m m' _ =>
      let k0 := blockKey sha256 (bytesAt m key keyLen.toNat)
      Repr m' inner (xorPad k0 ipad) ∧ Repr m' outer (xorPad k0 opad))
    (writeArgs := true)
    (stack := stack)

/-- `vg_hmac_sha256_init` on the 32-bit targets. -/
def initSha256Api : Api where
  module := "hmac_sha256"
  name := "vg_hmac_sha256_init"
  sig := initSha256Sig
  writeArgs := true
  contracts := some fun A stack => initSha256Contract A stack
  summary := "Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the SHA-256 \
    streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` \
    is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then \
    absorbed with `vg_sha256_update` on `*inner` (its `count` starting at 64), and the MAC \
    computed with `vg_hmac_sha256_finalize`.\n\n\
    Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and `key_len` \
    may affect timing, not the key."
  safety := [
    "`key_len` must be at most 64.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 86])`,
on 32-bit targets. `count` is public; `inner` is left unspecified, and
`scratch` is working space. -/
def finalizeSha256OutSig : Sig where
  params := [("inner", .array true .u8 96), ("outer", .array false .u8 96),
    ("count", .int .u64 true), ("out", .array true .u8 32), ("scratch", .array true .u64 86)]

/-- If, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under `K₀`
to `out`. The states are secret. -/
def finalizeSha256OutContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSha256OutSig.contract A (post := fun inner outer count out _scratch m m' _ =>
    ∀ k0 text, k0.length = 64 → Repr m inner (xorPad k0 ipad ++ text) →
      count = BitVec.ofNat 64 (64 + text.length) → Repr m outer (xorPad k0 opad) →
      bytesAt m' out 32 = hmacBlockKey sha256 k0 text)
    (writeArgs := true)
    (stack := stack)

/-- `vg_hmac_sha256_finalize` on the 32-bit targets. -/
def finalizeSha256OutApi : Api where
  module := "hmac_sha256"
  name := "vg_hmac_sha256_finalize"
  sig := finalizeSha256OutSig
  writeArgs := true
  contracts := some fun A stack => finalizeSha256OutContract A stack
  summary := "Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the \
    SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo \
    2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under `K₀` to \
    `*out`.\n\n\
    Contract: `VG.Spec.Hmac.finalizeSha256OutContract`. Constant time: only the pointers and \
    `count` may affect timing, not the states."
  safety := [
    "The contents of `inner` on return are unspecified.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Hmac

import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# PBKDF2-HMAC-SHA-256: the contract of its iteration, on the 32-bit targets

**Trusted** (as every file in `Spec/`). The expensive part of PBKDF2 is
step 3's chain `Uⱼ₊₁ = PRF (P, Uⱼ)`, whose outputs are exclusive-or'ed into
`T` (`VG.Spec.Pbkdf2.iterate`). `vg_pbkdf2_hmac_sha256_iterate` computes it,
with the password's HMAC-SHA-256 key given as the two streaming states that
`vg_hmac_sha256_init` sets up (`VG.Spec.Hmac.initSha256Contract`), at offsets
0 (inner) and 96 (outer) of `key`.

This contract is, definitionally, `VG.Spec.Hmac.sha256I.iterateContract`
(`Spec/Pbkdf2/Generic.lean`, which also has the contract of
`vg_pbkdf2_hmac_sha256`, the whole of PBKDF2-HMAC-SHA-256, as it has every
hash function's). The implementations on the 32-bit targets are proven
against this one; it is removed once SHA-256 is implemented through `sha256I`
on every target, as it already is on the 64-bit ones.

`A` is the target's calling convention. The signature fixes where the
arguments are, the memory the function may access, disjointness, and that
the pointers and the iteration count are public (see `TCB/Sig.lean`); the
contract adds the rest. The function may overwrite its arguments passed in
memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions it calls; `stack` is the number of bytes of stack
below the stack pointer that an implementation's calls use (see
`Sig.contract`), which depends on the target.
-/

namespace VG.Spec.Pbkdf2

open Sha256 (Repr bytesAt)
open Hmac (xorPad ipad opad hmacBlockKey sha256)

/-- `vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 104])`.
`n` is public; `scratch` is working space. -/
def iterateSha256Sig : Sig where
  params := [("key", .array false .u8 192), ("u", .array false .u8 32), ("n", .int .u32 true),
    ("t", .array true .u8 32), ("scratch", .array true .u64 104)]

/-- If, for a 64-byte key `K₀`, the streaming state at `key` represents
`K₀ ⊕ ipad` and the one at `key + 96` represents `K₀ ⊕ opad`: from the 32
bytes `U` at `u` and `T` at `t`, runs `n` steps `U ← HMAC-SHA-256 (K₀, U)`,
`T ← T ⊕ U`, leaving the final `T` at `t`. The key, `U` and `T` are secret. -/
def iterateSha256Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  iterateSha256Sig.contract A (post := fun key u n t _scratch m m' _ =>
    ∀ k0, k0.length = 64 → Repr m key (xorPad k0 ipad) → Repr m (key + 96) (xorPad k0 opad) →
      bytesAt m' t 32 = iterate (hmacBlockKey sha256 k0) n.toNat (bytesAt m u 32) (bytesAt m t 32))
    (writeArgs := true)
    (stack := stack)

/-- `vg_pbkdf2_hmac_sha256_iterate` on the 32-bit targets. -/
def iterateSha256Api : Api where
  module := "pbkdf2_sha256"
  name := "vg_pbkdf2_hmac_sha256_iterate"
  sig := iterateSha256Sig
  writeArgs := true
  contracts := some fun A stack => iterateSha256Contract A stack
  summary := "Runs `n` steps of PBKDF2-HMAC-SHA-256's iteration: if, for a 64-byte key `K₀`, the \
    SHA-256 streaming state in bytes 0 to 95 of `*key` represents `K₀ ⊕ ipad` and the one in bytes \
    96 to 191 represents `K₀ ⊕ opad` (as `vg_hmac_sha256_init` leaves them), repeats \
    `U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u` and `T = *t`, and leaves the \
    final `T` in `*t` (RFC 8018, step 3 of `F`).\n\n\
    Contract: `VG.Spec.Pbkdf2.iterateSha256Contract`. Constant time: only the pointers and `n` may \
    affect timing, not the key, `U` or `T`."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.Pbkdf2

import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Spec.Hmac.Generic

/-!
# PBKDF2-HMAC over any streaming hash function: the contract of its iteration, on every target

**Trusted** (as every file in `Spec/`). The contract of
`VG.Spec.Pbkdf2.iterateSha256Contract` (`Spec/Pbkdf2/Contract.lean`) with the
hash function a parameter (`VG.Spec.Hmac.StreamingHash`):
`vg_pbkdf2_hmac_<hash>_iterate` computes step 3's chain
`Uⱼ₊₁ = PRF (P, Uⱼ)`, exclusive-or'ed into `T` (`VG.Spec.Pbkdf2.iterate`),
with the password's HMAC key given as the two streaming states that
`vg_hmac_<hash>_init` sets up (`VG.Spec.Hmac.initContract`), one after the
other in `key`. `U` and `T` are as long as the digest.

`A` is the target's calling convention. `scratch` is the number of 64-bit
words of working space, which depends on the implementation; `stack` is the
number of bytes of stack below the stack pointer that an implementation's
calls use (see `Sig.contract`). The function may overwrite its arguments
passed in memory, where the calling convention allows it (`writeArgs`), to
pass arguments to the functions it calls.
-/

namespace VG.Spec.Pbkdf2

open Sha256 (bytesAt)
open Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

variable (S : StreamingHash) (scratch : Nat)

/-- `vg_pbkdf2_hmac_<hash>_iterate(key: *const [u8; 2S], u: *const [u8; D], n: u32, t: *mut [u8; D], scratch: *mut [u64; W])`,
with `S` the size of the streaming state and `D` that of the digest. `n` is
public; `scratch` is working space. -/
def iterateSig : Sig where
  params := [("key", .array false .u8 (2 * S.stateBytes)), ("u", .array false .u8 S.digestBytes),
    ("n", .int .u32 true), ("t", .array true .u8 S.digestBytes), ("scratch", .array true .u64 scratch)]

/-- If, for a key `K₀` of the block size of `H`, the streaming state at `key`
represents `K₀ ⊕ ipad` and the one right after it represents `K₀ ⊕ opad`:
from the digest-sized `U` at `u` and `T` at `t`, runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U`, leaving the final `T` at `t`. The key, `U`
and `T` are secret. -/
def iterateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (iterateSig S scratch).contract A (post := fun key u n t _scratch m m' _ =>
    ∀ k0, k0.length = S.H.blockSize → S.Repr m key (xorPad k0 ipad) →
      S.Repr m (key + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
      bytesAt m' t S.digestBytes =
        iterate (hmacBlockKey S.H k0) n.toNat (bytesAt m u S.digestBytes) (bytesAt m t S.digestBytes))
    (writeArgs := true)
    (stack := stack)

end VG.Spec.Pbkdf2

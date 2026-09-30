import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Spec.Hmac.Generic

/-!
# PBKDF2-HMAC over any streaming hash function: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contract of
`VG.Spec.Pbkdf2.iterateSha256Contract` (`Spec/Pbkdf2/Contract.lean`) with the
hash function a parameter (`VG.Spec.Hmac.StreamingHash`):
`vg_pbkdf2_hmac_<hash>_iterate` computes step 3's chain
`Uⱼ₊₁ = PRF (P, Uⱼ)`, exclusive-or'ed into `T` (`VG.Spec.Pbkdf2.iterate`),
with the password's HMAC key given as the two streaming states that
`vg_hmac_<hash>_init` sets up (`VG.Spec.Hmac.initContract`), one after the
other in `key`. `U` and `T` are as long as the digest.

`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers, the lengths and the iteration counts are public (see
`TCB/Sig.lean`); the contracts add the rest. `scratch` is the number of 64-bit
words of working space, which depends on the implementation; `stack` is the
number of bytes of stack below the stack pointer that an implementation's
calls use (see `Sig.contract`). The functions may overwrite their arguments
passed in memory, where the calling convention allows it (`writeArgs`), to
pass arguments to the functions it calls.

`vg_pbkdf2_hmac_<hash>` computes the whole of PBKDF2-HMAC with that hash
function (`VG.Spec.Pbkdf2.pbkdf2Hmac`): the key (hashing a password longer
than a block), `U₁` of each block, which absorbs the salt, the iteration,
and the truncation, composed from the verified functions by calls.

`VG.Spec.Hmac.Instance.iterateApi` and `VG.Spec.Hmac.Instance.pbkdf2Api`
are the functions of an `Instance` in the Rust interface.
-/

namespace VG.Spec.Pbkdf2

open Sha256 (bytesAt)
open Hmac (StreamingHash xorPad ipad opad hmacBlockKey hmac)

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

/-- PBKDF2 with HMAC over the hash function of `S` (RFC 2104, FIPS 198-1) as
the pseudorandom function, keyed with the password `p` (`hLen` is the size of
the digest). -/
def pbkdf2Hmac (p s : List Byte) (c dkLen : Nat) : Option (List Byte) :=
  pbkdf2 (hmac S.H p) S.digestBytes s c dkLen

/-- `vg_pbkdf2_hmac_<hash>(password: *const u8, password_len: usize, salt: *const u8, salt_len: usize, c: u32, out: *mut u8, out_len: usize, scratch: *mut [u64; W])`.
The iteration count `c` and the lengths are public; `scratch` is working
space. -/
def pbkdf2Sig : Sig where
  params := [("password", .slice false .u8 "password_len"), ("salt", .slice false .u8 "salt_len"),
    ("c", .int .u32 true), ("out", .slice true .u8 "out_len"), ("scratch", .array true .u64 scratch)]

/-- If `c` is positive and `out_len` at most `(2³² − 1) · D`, with `D` the
size of the digest (so that PBKDF2 accepts it): writes
`PBKDF2-HMAC (P, S, c, out_len)` of the `password_len` bytes `P` at
`password` and the `salt_len` bytes `S` at `salt` to the `out_len` bytes at
`out`. The password, the salt and the derived key are secret. -/
def pbkdf2Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (pbkdf2Sig scratch).contract A
    (pre := fun _password _passwordLen _salt _saltLen c _out outLen _scratch _m =>
      0 < c.toNat ∧ outLen.toNat ≤ (2 ^ 32 - 1) * S.digestBytes)
    (post := fun password passwordLen salt saltLen c out outLen _scratch m m' _ =>
      pbkdf2Hmac S (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat)
        c.toNat outLen.toNat = some (bytesAt m' out outLen.toNat))
    (writeArgs := true)
    (stack := stack)

end VG.Spec.Pbkdf2

namespace VG.Spec.Hmac.Instance

variable (I : Instance)

/-- The contract of `vg_pbkdf2_hmac_<hash>_iterate`: `VG.Spec.Pbkdf2.iterateContract`. -/
def iterateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Pbkdf2.iterateContract I.S I.scratch A stack

/-- `vg_pbkdf2_hmac_<hash>_iterate` on every target. -/
def iterateApi : Api where
  module := s!"pbkdf2_{I.rust}"
  name := s!"vg_pbkdf2_hmac_{I.rust}_iterate"
  sig := Pbkdf2.iterateSig I.S I.scratch
  summary := s!"Runs `n` steps of PBKDF2-HMAC-{I.alg}'s iteration: if, for a \
    {I.S.H.blockSize}-byte key `K₀`, the {I.alg} streaming state in bytes 0 to \
    {I.S.stateBytes - 1} of `*key` represents `K₀ ⊕ ipad` and the one in bytes {I.S.stateBytes} \
    to {2 * I.S.stateBytes - 1} represents `K₀ ⊕ opad` (as `vg_hmac_{I.rust}_init` leaves them), \
    repeats `U ← HMAC-{I.alg} (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u` and `T = *t`, and \
    leaves the final `T` in `*t` (RFC 8018, step 3 of `F`).\n\n\
    Contract: `VG.Spec.Hmac.Instance.iterateContract` of `VG.Spec.Hmac.{I.lean}`. Constant \
    time: only the pointers and `n` may affect timing, not the key, `U` or `T`."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- The number of 64-bit words of working space of `vg_pbkdf2_hmac_<hash>`:
that of the functions it calls (`scratch`), then a word for each byte of the
streaming state, for its own buffers (the HMAC key's two streaming states, a
third one for `U₁` and for hashing a long password, the digests `U` and `T`
and the hashed password, `INT (i)`) and spills. -/
def pbkdf2Scratch : Nat := I.scratch + I.S.stateBytes

/-- The contract of `vg_pbkdf2_hmac_<hash>`: `VG.Spec.Pbkdf2.pbkdf2Contract`. -/
def pbkdf2Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Pbkdf2.pbkdf2Contract I.S I.pbkdf2Scratch A stack

/-- `vg_pbkdf2_hmac_<hash>` on every target. -/
def pbkdf2Api : Api where
  module := s!"pbkdf2_{I.rust}"
  name := s!"vg_pbkdf2_hmac_{I.rust}"
  sig := Pbkdf2.pbkdf2Sig I.pbkdf2Scratch
  writeArgs := true
  summary := s!"PBKDF2-HMAC-{I.alg} (RFC 8018 §5.2, with HMAC-{I.alg} as the pseudorandom \
    function): writes the `out_len`-byte key derived from the `password_len` bytes at `password` \
    and the `salt_len` bytes at `salt` with `c` iterations to `out`. Calls the verified {I.alg} \
    and HMAC-{I.alg} functions and `vg_pbkdf2_hmac_{I.rust}_iterate`.\n\n\
    Contract: `VG.Spec.Hmac.Instance.pbkdf2Contract` of `VG.Spec.Hmac.{I.lean}`. Constant time: \
    only the pointers, the lengths and `c` may affect timing, not the password, the salt or the \
    key."
  safety := [
    s!"`c` must be positive, and `out_len` at most `(2^32 - 1) * {I.S.digestBytes}`.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Hmac.Instance

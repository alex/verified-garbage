import VerifiedGarbage.Spec.Scrypt
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.TCB.Artifact

/-!
# scrypt: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the Salsa20/8 Core
(`vg_salsa20_8`), scryptBlockMix (`vg_scrypt_blockmix`) and scryptROMix
(`vg_scrypt_romix`), in terms of `Spec/Scrypt.lean`, for any target: `A` is
the target's calling convention. The signatures fix where the arguments are,
the memory each function may access, disjointness, and that the pointers
and lengths are public (see `TCB/Sig.lean`). Each function may overwrite its
arguments passed in memory, where the calling convention allows it
(`writeArgs`), to pass arguments to the functions it calls; `stack` is the
number of bytes of stack below the stack pointer that an implementation's
calls and frames use (see `Sig.contract`), which depends on the target.

`vg_scrypt` computes the whole of scrypt (`Scrypt.scrypt`): the two
PBKDF2-HMAC-SHA-256 steps (`vg_pbkdf2_hmac_sha256`) and scryptROMix of each
of the `p` blocks, composed from the verified functions by calls. The caller
provides the memory, whose size depends on the parameters.

The working space is sized for the tightest target, x86-64, whose model has
no stack frames: each function keeps its callee's working space at the start
of its own and saves its caller's registers after it (Salsa20/8: 64 bytes;
scryptBlockMix: Salsa20/8's, then 64 bytes; scryptROMix: scryptBlockMix's,
64 bytes, then `T = X xor V[j]`).

scryptROMix reads the blocks `V[j]` at indices `j` computed from the
password (§5), so its memory accesses depend on them: its contract declares
that it leaks them (`Scrypt.roMixIndices`, through `Sig.contract`'s `leak`),
and nothing else secret.
-/

namespace VG.Spec.Scrypt

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32; 16])`. `scratch` is
working space. -/
def salsaSig : Sig where
  params := [("b", .array true .u8 64), ("scratch", .array true .u32 16)]

/-- Replaces the 64 bytes at `b` by their Salsa20/8 Core, which are secret. -/
def salsaContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  salsaSig.contract A (post := fun b _scratch m m' _ =>
    bytesAt m' b 64 = salsa (bytesAt m b 64))
    (writeArgs := true)
    (stack := stack)

/-- `vg_salsa20_8` on every target. -/
def salsaApi : Api where
  module := "scrypt"
  name := "vg_salsa20_8"
  sig := salsaSig
  writeArgs := true
  contracts := some fun A stack => salsaContract A stack
  summary := "The Salsa20/8 Core (RFC 7914 §3): replaces the 64 bytes `*b` by their Salsa20/8 Core \
    (the 16 little-endian words, 8 rounds, then the input added word by word).\n\n\
    Contract: `VG.Spec.Scrypt.salsaContract`. Constant time: only the pointers may affect timing, \
    not the data."
  safety := [
    "`scratch` is working space: its contents on return are unspecified."]

/-- `vg_scrypt_blockmix(b: *const [u8; 128], r: usize, y: *mut [u8; 128], ry: usize, scratch: *mut [u32; 32])`.
`b` and `y` are the input and the output, of `r` and `ry` 128-byte chunks;
`scratch` is working space. -/
def blockMixSig : Sig where
  params := [("b", .slice false (.array .u8 128) "r"), ("y", .slice true (.array .u8 128) "ry"),
    ("scratch", .array true .u32 32)]

/-- If `ry = r` and `r` is positive: writes scryptBlockMix with block size
parameter `r` of the `128 * r` bytes at `b` to the `128 * r` bytes at `y`.
The data is secret. -/
def blockMixContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockMixSig.contract A
    (pre := fun _b r _y ry _scratch _m => ry = r ∧ 0 < r.toNat)
    (post := fun b r y _ry _scratch m m' _ =>
      bytesAt m' y (128 * r.toNat) = blockMix r.toNat (bytesAt m b (128 * r.toNat)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_scrypt_blockmix` on every target. -/
def blockMixApi : Api where
  module := "scrypt"
  name := "vg_scrypt_blockmix"
  sig := blockMixSig
  writeArgs := true
  contracts := some fun A stack => blockMixContract A stack
  summary := "scryptBlockMix (RFC 7914 §4) with block size parameter `r`: writes scryptBlockMix of \
    the `128 * r` bytes at `b` to the `128 * ry` bytes at `y`. Calls `vg_salsa20_8` for each \
    64-byte block.\n\n\
    Contract: `VG.Spec.Scrypt.blockMixContract`. Constant time: only the pointers and `r` may \
    affect timing, not the data."
  safety := [
    "`ry` must equal `r`, and `r` must be positive.",
    "`scratch` is working space: its contents on return are unspecified."]

/-- `vg_scrypt_romix(b: *mut [u8; 128], r: usize, v: *mut [u8; 128], vlen: usize, scratch: *mut [u8; 128], slen: usize)`.
`b` holds `B`, of `r` 128-byte chunks; `v`, of `vlen = N * r` chunks, is
where step 2 writes `V[0], …, V[N - 1]`; `scratch`, of `r + 2` chunks, is
working space. -/
def roMixSig : Sig where
  params := [("b", .slice true (.array .u8 128) "r"), ("v", .slice true (.array .u8 128) "vlen"),
    ("scratch", .slice true (.array .u8 128) "slen")]

/-- If `r` is positive, `vlen = N * r` for a power of two `N`, and
`slen = r + 2`: replaces the `128 * r` bytes at `b` by their scryptROMix
with block size parameter `r` and cost parameter `N`. The data is secret,
but the indices `j` of step 3 (`roMixIndices`) may leak. -/
def roMixContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  roMixSig.contract A
    (pre := fun _b r _v vlen _scratch slen _m =>
      0 < r.toNat ∧ vlen.toNat % r.toNat = 0 ∧ (vlen.toNat / r.toNat).isPowerOfTwo ∧
        slen.toNat = r.toNat + 2)
    (post := fun b r _v vlen _scratch _slen m m' _ =>
      bytesAt m' b (128 * r.toNat) =
        roMix r.toNat (vlen.toNat / r.toNat) (bytesAt m b (128 * r.toNat)))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun b r _v vlen _scratch _slen m =>
      roMixIndices r.toNat (vlen.toNat / r.toNat) (bytesAt m b (128 * r.toNat)))

/-- `vg_scrypt_romix` on every target. -/
def roMixApi : Api where
  module := "scrypt"
  name := "vg_scrypt_romix"
  sig := roMixSig
  writeArgs := true
  contracts := some fun A stack => roMixContract A stack
  summary := "scryptROMix (RFC 7914 §5) with block size parameter `r` and cost parameter \
    `N = vlen / r`: replaces the `128 * r` bytes at `b` by their scryptROMix. Step 2 writes \
    `V[0], …, V[N - 1]` to `v`. Calls `vg_scrypt_blockmix` for each scryptBlockMix.\n\n\
    Contract: `VG.Spec.Scrypt.roMixContract`. Not constant time in the indices: timing may depend \
    on the pointers, `r`, `N` and the indices `j` of step 3 (`VG.Spec.Scrypt.roMixIndices`), which \
    are derived from the data and so leak information about it (as in every scrypt that indexes \
    `V` directly), but on nothing else."
  safety := [
    "`r` must be positive, `vlen` must be `N * r` for a power of two `N`, and `slen` must be \
      `r + 2`.",
    "`v` and `scratch` are working space: their contents on return are unspecified."]

/-- `vg_scrypt(password: *const u8, password_len: usize, salt: *const u8, salt_len: usize, r: usize, b: *mut [u8; 128], blen: usize, v: *mut [u8; 128], vlen: usize, scratch: *mut [u8; 128], slen: usize, out: *mut u8, out_len: usize)`.
The block size parameter `r` and the lengths are public. `b`, of
`blen = p * r` 128-byte chunks, holds `B`; `v`, of `vlen = N * r` chunks, is
scryptROMix's `V`; `scratch`, of `slen = r + 16` chunks, is working space. -/
def scryptSig : Sig where
  params := [("password", .slice false .u8 "password_len"), ("salt", .slice false .u8 "salt_len"),
    ("r", .int .usize true), ("b", .slice true (.array .u8 128) "blen"),
    ("v", .slice true (.array .u8 128) "vlen"), ("scratch", .slice true (.array .u8 128) "slen"),
    ("out", .slice true .u8 "out_len")]

/-- The blocks `B[0], …, B[p - 1]` of scrypt's step 1: its `p` chunks of
`128 * r` bytes of `PBKDF2-HMAC-SHA256 (P, S, 1, p * 128 * r)`. -/
def blocks (pw s : List Byte) (r p : Nat) : List (List Byte) :=
  let b := (Pbkdf2.pbkdf2HmacSha256 pw s 1 (p * 128 * r)).getD []
  (List.range p).map fun i => (b.drop (128 * r * i)).take (128 * r)

/-- If `r` is positive, `blen = p * r` and `vlen = N * r` for parameters
`N`, `r`, `p` and `out_len` that are `valid` and that PBKDF2 accepts
(`out_len ≤ (2³² − 1) · 32`), and `slen = r + 16`: writes
`scrypt (P, S, N, r, p, out_len)` of the `password_len` bytes `P` at
`password` and the `salt_len` bytes `S` at `salt` to the `out_len` bytes at
`out`. The password, the salt and the derived key are secret, but the
indices `j` of each scryptROMix's step 3 (`roMixIndices` of each block
`B[i]`, in order) may leak. -/
def scryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scryptSig.contract A
    (pre := fun _password _passwordLen _salt _saltLen r _b blen _v vlen _scratch slen _out outLen
        _m =>
      0 < r.toNat ∧ blen.toNat % r.toNat = 0 ∧ vlen.toNat % r.toNat = 0 ∧
        valid (vlen.toNat / r.toNat) r.toNat (blen.toNat / r.toNat) outLen.toNat ∧
        outLen.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r.toNat + 16)
    (post := fun password passwordLen salt saltLen r _b blen _v vlen _scratch _slen out outLen m
        m' _ =>
      scrypt (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat)
        (vlen.toNat / r.toNat) r.toNat (blen.toNat / r.toNat) outLen.toNat =
        some (bytesAt m' out outLen.toNat))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun password passwordLen salt saltLen r _b blen _v vlen _scratch _slen _out
        _outLen m =>
      (blocks (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat) r.toNat
        (blen.toNat / r.toNat)).flatMap (roMixIndices r.toNat (vlen.toNat / r.toNat)))

/-- `vg_scrypt` on every target. -/
def scryptApi : Api where
  module := "scrypt"
  name := "vg_scrypt"
  sig := scryptSig
  writeArgs := true
  contracts := some fun A stack => scryptContract A stack
  summary := "scrypt (RFC 7914 §6) with block size parameter `r`, cost parameter `N = vlen / r` \
    and parallelization parameter `p = blen / r`: writes the `out_len`-byte key derived from the \
    `password_len` bytes at `password` and the `salt_len` bytes at `salt` to `out`. Calls \
    `vg_pbkdf2_hmac_sha256` for its two PBKDF2-HMAC-SHA256 steps and `vg_scrypt_romix` for each \
    of the `p` blocks.\n\n\
    Contract: `VG.Spec.Scrypt.scryptContract`. Not constant time in the indices: timing may \
    depend on the pointers, the lengths, `r`, `N`, `p` and the indices `j` of step 3 of each \
    scryptROMix, which are derived from the password and the salt and so leak information about \
    them (as in every scrypt that indexes `V` directly), but on nothing else."
  safety := [
    "`r` must be positive, `blen` must be `p * r` and `vlen` must be `N * r` for parameters that \
      RFC 7914 §6 accepts (`N` a power of two greater than 1 and less than `2^(16 r)`, \
      `0 < p ≤ (2^32 - 1) * 32 / (128 r)`, `0 < out_len ≤ (2^32 - 1) * 32`), and `slen` must be \
      `r + 16`.",
    "`b`, `v` and `scratch` are working space: their contents on return are unspecified."]

end VG.Spec.Scrypt

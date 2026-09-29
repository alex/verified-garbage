import VerifiedGarbage.Spec.Scrypt
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

The rest of scrypt (the two PBKDF2-HMAC-SHA-256 steps, and the loop over the
`p` blocks) is composed from the verified functions by the caller.

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
  summary := "The Salsa20/8 Core (RFC 7914 §3): replaces the 64 bytes `*b` by their Salsa20/8 Core \
    (the 16 little-endian words, 8 rounds, then the input added word by word).\n\n\
    Contract: `VG.Spec.Scrypt.salsaContract`. Constant time: only the pointers may affect timing, \
    not the data."
  safety := [
    "`b` must be valid for reads and writes of 64 bytes.",
    "`scratch` must be valid for reads and writes of 64 bytes. It is working space: its contents \
      on return are unspecified."]

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
  summary := "scryptBlockMix (RFC 7914 §4) with block size parameter `r`: writes scryptBlockMix of \
    the `128 * r` bytes at `b` to the `128 * ry` bytes at `y`. Calls `vg_salsa20_8` for each \
    64-byte block.\n\n\
    Contract: `VG.Spec.Scrypt.blockMixContract`. Constant time: only the pointers and `r` may \
    affect timing, not the data."
  safety := [
    "`ry` must equal `r`, and `r` must be positive.",
    "`b` must be valid for reads of `128 * r` bytes, and `y` for reads and writes of `128 * ry` \
      bytes.",
    "`scratch` must be valid for reads and writes of 128 bytes. It is working space: its contents \
      on return are unspecified."]

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
    "`b` must be valid for reads and writes of `128 * r` bytes, `v` of `128 * vlen` bytes and \
      `scratch` of `128 * slen` bytes. `v` and `scratch` are working space: their contents on \
      return are unspecified."]

end VG.Spec.Scrypt

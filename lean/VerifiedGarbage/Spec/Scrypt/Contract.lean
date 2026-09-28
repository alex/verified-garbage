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

/-- `vg_scrypt_blockmix(b: *const [u8; 128], r: usize, y: *mut [u8; 128], ry: usize, scratch: *mut [u32; 16])`.
`b` and `y` are the input and the output, of `r` and `ry` 128-byte chunks;
`scratch` is working space. -/
def blockMixSig : Sig where
  params := [("b", .slice false (.array .u8 128) "r"), ("y", .slice true (.array .u8 128) "ry"),
    ("scratch", .array true .u32 16)]

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

/-- `vg_scrypt_romix(b: *mut [u8; 128], r: usize, v: *mut [u8; 128], vlen: usize, scratch: *mut [u8; 128], slen: usize)`.
`b` holds `B`, of `r` 128-byte chunks; `v`, of `vlen = N * r` chunks, is
where step 2 writes `V[0], …, V[N - 1]`; `scratch`, of `r + 1` chunks, is
working space. -/
def roMixSig : Sig where
  params := [("b", .slice true (.array .u8 128) "r"), ("v", .slice true (.array .u8 128) "vlen"),
    ("scratch", .slice true (.array .u8 128) "slen")]

/-- If `r` is positive, `vlen = N * r` for a power of two `N`, and
`slen = r + 1`: replaces the `128 * r` bytes at `b` by their scryptROMix
with block size parameter `r` and cost parameter `N`. The data is secret,
but the indices `j` of step 3 (`roMixIndices`) may leak. -/
def roMixContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  roMixSig.contract A
    (pre := fun _b r _v vlen _scratch slen _m =>
      0 < r.toNat ∧ vlen.toNat % r.toNat = 0 ∧ (vlen.toNat / r.toNat).isPowerOfTwo ∧
        slen.toNat = r.toNat + 1)
    (post := fun b r _v vlen _scratch _slen m m' _ =>
      bytesAt m' b (128 * r.toNat) =
        roMix r.toNat (vlen.toNat / r.toNat) (bytesAt m b (128 * r.toNat)))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun b r _v vlen _scratch _slen m =>
      roMixIndices r.toNat (vlen.toNat / r.toNat) (bytesAt m b (128 * r.toNat)))

end VG.Spec.Scrypt

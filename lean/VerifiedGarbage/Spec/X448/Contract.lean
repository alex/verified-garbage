import VerifiedGarbage.Spec.X448
import VerifiedGarbage.TCB.Artifact

/-!
# X448: the contract, on every target

**Trusted** (as every file in `Spec/`). `Sig.contract` fixes argument
placement, buffer validity, separation and public pointers. Both scalar
and u-coordinate contents are secret. No input encodings are excluded.

The function takes 8 KiB of working space for field arithmetic and the
Montgomery ladder. Its contents on return are unspecified and may contain
secrets. `stack` is the number of bytes below the stack pointer used by an
implementation's calls and frames.

As with X25519, this single primitive supports public-key derivation using
the base point and key exchange using a peer's public key. Key generation,
byte import/export and the all-zero shared-secret check belong to the Rust
wrapper. They need no separate assembly entry points.
-/

namespace VG.Spec.X448

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- `vg_x448(out: *mut [u8; 56], scalar: *const [u8; 56], point: *const [u8; 56], scratch: *mut [u64; 1024])`.
`scratch` is working space. -/
def x448Sig : Sig where
  params := [("out", .array true .u8 56), ("scalar", .array false .u8 56),
    ("point", .array false .u8 56), ("scratch", .array true .u64 1024)]

/-- Writes `X448(k, u)` to `out`, for the 56-byte scalar `k` at `scalar`
and the 56-byte u-coordinate `u` at `point`. -/
def x448Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  x448Sig.contract A (post := fun out scalar point _scratch m m' _ =>
    bytesAt m' out 56 = x448 (bytesAt m scalar 56) (bytesAt m point 56))
    (stack := stack)

/-- `vg_x448` on every target. -/
def x448Api : Api where
  module := "x448"
  name := "vg_x448"
  sig := x448Sig
  summary := "Computes X448 (RFC 7748 §5): writes `X448(k, u)` to `*out`, for the 56-byte \
    scalar `k` at `scalar` and the 56-byte u-coordinate `u` at `point`. The scalar is \
    decoded (clamped); all 448 bits of `u` are used and noncanonical coordinates are \
    reduced modulo the field prime. The result may be all zero (for a `u` of small \
    order), which the caller must check for if its protocol requires it (RFC 7748 §6.2).\n\n\
    Contract: `VG.Spec.X448.x448Contract`. Constant time: only the pointers may affect \
    timing, not the scalar or the u-coordinate."
  safety := ["The contents of `scratch` on return are unspecified and may contain secrets; \
    the caller must destroy them after use."]

end VG.Spec.X448

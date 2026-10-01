import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 signing with a cached public key

**Trusted** (as every file in `Spec/`). RFC 8032 §5.1.6 uses the public key
`A` derived in §5.1.5. A caller may retain that key instead of deriving it
again for every signature. This contract requires that correspondence
explicitly and retains the complete `sign seed message` postcondition,
including every SHA-512 invocation. It does not specify a signature for
an independently chosen seed/public-key pair.

The seed-only `signContract` remains available unchanged. This additional
entry point lets `SigningKey`, which stores a seed and its derived public
key together, call one verified signing operation without repeating the
public-key scalar multiplication. No buffer contents may affect timing,
including the cached public key.
-/

namespace VG.Spec.Ed25519

/-- `(out: *mut [u8; 64], seed: *const [u8; 32], pk: *const [u8; 32],
message: *const u8, len: usize, scratch: *mut [u64; 1024])`. -/
def signCachedSig : Sig where
  params := [("out", .array true .u8 64), ("seed", .array false .u8 32),
    ("pk", .array false .u8 32), ("message", .slice false .u8 "len"),
    ("scratch", .array true .u64 scratchWords)]

/-- Sign with the public key corresponding to the seed. The postcondition
is the same complete signing algorithm as `signContract`. -/
def signCachedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signCachedSig.contract A
    (pre := fun _out seed pk _message _len _scratch m =>
      bytesAt m pk 32 = publicKey (bytesAt m seed 32))
    (post := fun out seed _pk message len _scratch m m' _ =>
      bytesAt m' out 64 = sign (bytesAt m seed 32) (bytesAt m message len.toNat))
    (writeArgs := true) (stack := stack)

/-- Complete signing with a cached, matching public key, on every target. -/
def signCachedApi : Api where
  module := "ed25519"
  name := "vg_ed25519_sign_cached"
  sig := signCachedSig
  writeArgs := true
  contracts := some fun A stack => signCachedContract A stack
  summary := "Deterministic Ed25519 signing (RFC 8032 §5.1.6): writes the 64-byte signature \
    to `*out`, for the `len` bytes at `message` and the 32-byte private seed at `seed`, \
    using its cached public key at `pk`. Includes all hashing, pruning and scalar/group \
    operations. Uses pure Ed25519, with no context or prehash. \
    Contract: `VG.Spec.Ed25519.signCachedContract`. Constant time: only pointers and the \
    message length may affect timing, not any buffer contents."
  safety := [
    "The 32 bytes at `pk` must equal the public key derived from the 32 bytes at `seed` \
      by RFC 8032 §5.1.5 (`VG.Spec.Ed25519.publicKey`).",
    "`seed` must originate from a cryptographically secure random generator.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the \
      caller must destroy them after use."]

end VG.Spec.Ed25519

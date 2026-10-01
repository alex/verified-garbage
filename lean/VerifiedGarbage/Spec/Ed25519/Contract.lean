import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.TCB.Artifact

/-!
# Ed25519: contracts on every target

**Trusted** (as every file in `Spec/`). The signatures determine memory
validity, separation, and public pointers and lengths through `Sig.contract`.
Key derivation and signing keep all buffer contents secret. Verification
may leak its inputs; it returns exactly 0 or 1. There are no failure or
retry allowances for key derivation or signing.

The scalar and group primitives allow composition with the existing SHA-512
API. The complete-operation contracts also specify the hashing, so that an
assembly caller can be verified end to end, generic over SHA-512 backends.
`verifyEquation` alone checks a supplied challenge; its documentation does
not claim it hashes the message, and states that `verify`'s predicate needs
the challenge reduced modulo `L` (with `scalarReduce`) before the call.

All functions take 8 KiB of scratch space, whose contents are unspecified on
return and must be destroyed by callers handling secrets. `stack` describes
the space used below the stack pointer. `writeArgs` allows calls to reuse
the ABI's argument slots, including on 32-bit targets.
-/

namespace VG.Spec.Ed25519

/-- Bytes in a buffer, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- Working space in `u64`s, shared by all target signatures. -/
def scratchWords : Nat := 1024

private def scratchSafety : String :=
  "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
    must destroy them after use."

/-! ## Scalar and group primitives -/

/-- `(out: *mut [u8; 32], scalar: *const [u8; 32], scratch: *mut [u64; 1024])`. -/
def scalarBaseSig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("scratch", .array true .u64 scratchWords)]

/-- Encode `[s]B`, for the entire unsigned 256-bit scalar, without pruning. -/
def scalarBaseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarBaseSig.contract A
    (post := fun out scalar _scratch m m' _ =>
      bytesAt m' out 32 = scalarBase (bytesAt m scalar 32))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 32], wide: *const [u8; 64], scratch: *mut [u64; 1024])`. -/
def scalarReduceSig : Sig where
  params := [("out", .array true .u8 32), ("wide", .array false .u8 64),
    ("scratch", .array true .u64 scratchWords)]

/-- Reduce all 512 input bits modulo `L`, returning a canonical scalar. -/
def scalarReduceContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarReduceSig.contract A
    (post := fun out wide _scratch m m' _ =>
      bytesAt m' out 32 = scalarReduce (bytesAt m wide 64))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 32], r: *const [u8; 32], k: *const [u8; 32], s: *const [u8; 32], scratch: *mut [u64; 1024])`. -/
def scalarMulAddSig : Sig where
  params := [("out", .array true .u8 32), ("r", .array false .u8 32),
    ("k", .array false .u8 32), ("s", .array false .u8 32),
    ("scratch", .array true .u64 scratchWords)]

/-- Compute `(r + k*s) mod L`. All three unsigned 256-bit inputs are secret;
they need not be reduced modulo `L`. -/
def scalarMulAddContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarMulAddSig.contract A
    (post := fun out r k s _scratch m m' _ =>
      bytesAt m' out 32 = scalarMulAdd (bytesAt m r 32) (bytesAt m k 32) (bytesAt m s 32))
    (writeArgs := true) (stack := stack)

/-- `(pk: *const [u8; 32], signature: *const [u8; 64], challenge: *const [u8; 64], scratch: *mut [u64; 1024]) -> u32`. -/
def verifyEquationSig : Sig where
  params := [("pk", .array false .u8 32), ("signature", .array false .u8 64),
    ("challenge", .array false .u8 64), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Check the encodings and equation using the full 512-bit challenge, as
given: no reduction modulo `L` takes place here, nor message hashing.
All inputs may affect timing. -/
def verifyEquationContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifyEquationSig.contract A
    (post := fun pk signature challenge _scratch m _m' r =>
      r = if verifyEquation (bytesAt m pk 32) (bytesAt m signature 64)
        (bytesAt m challenge 64) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk signature challenge _scratch m =>
      (bytesAt m pk 32 ++ bytesAt m signature 64 ++ bytesAt m challenge 64).map (·.toNat))

/-! ## Complete operations -/

/-- `(out: *mut [u8; 32], seed: *const [u8; 32], scratch: *mut [u64; 1024])`. -/
def publicKeySig : Sig where
  params := [("out", .array true .u8 32), ("seed", .array false .u8 32),
    ("scratch", .array true .u64 scratchWords)]

/-- Derive the public key from a seed, including SHA-512 and pruning. -/
def publicKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicKeySig.contract A
    (post := fun out seed _scratch m m' _ => bytesAt m' out 32 = publicKey (bytesAt m seed 32))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 64], seed: *const [u8; 32], message: *const u8, len: usize, scratch: *mut [u64; 1024])`. -/
def signSig : Sig where
  params := [("out", .array true .u8 64), ("seed", .array false .u8 32),
    ("message", .slice false .u8 "len"), ("scratch", .array true .u64 scratchWords)]

/-- Sign the message deterministically. Neither the seed nor message bytes
may affect timing; the message length is public. -/
def signContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signSig.contract A
    (post := fun out seed message len _scratch m m' _ =>
      bytesAt m' out 64 = sign (bytesAt m seed 32) (bytesAt m message len.toNat))
    (writeArgs := true) (stack := stack)

/-- `(pk: *const [u8; 32], message: *const u8, len: usize, signature: *const [u8; 64], scratch: *mut [u64; 1024]) -> u32`. -/
def verifySig : Sig where
  params := [("pk", .array false .u8 32), ("message", .slice false .u8 "len"),
    ("signature", .array false .u8 64), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Verify the signature, including the message hash. All inputs are public. -/
def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifySig.contract A
    (post := fun pk message len signature _scratch m _m' r =>
      r = if verify (bytesAt m pk 32) (bytesAt m message len.toNat)
        (bytesAt m signature 64) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk message len signature _scratch m =>
      (bytesAt m pk 32 ++ bytesAt m message len.toNat ++ bytesAt m signature 64).map (·.toNat))

/-! ## Emitted API documentation -/

def scalarBaseApi : Api where
  module := "ed25519"
  name := "vg_ed25519_scalar_base"
  sig := scalarBaseSig
  writeArgs := true
  contracts := some fun A stack => scalarBaseContract A stack
  summary := "Ed25519 base-point multiplication (RFC 8032 §5.1.4): writes the encoding of \
    `[s]B` to `*out`, for the unsigned little-endian 256-bit integer at `scalar`, without \
    pruning. Contract: `VG.Spec.Ed25519.scalarBaseContract`. Constant time: only pointers \
    may affect timing."
  safety := [scratchSafety]

def scalarReduceApi : Api where
  module := "ed25519"
  name := "vg_ed25519_scalar_reduce"
  sig := scalarReduceSig
  writeArgs := true
  contracts := some fun A stack => scalarReduceContract A stack
  summary := "Ed25519 scalar reduction (RFC 8032 §5.1.6): writes the canonical 32-byte \
    little-endian encoding of `wide mod L` to `*out`, using all 64 input bytes. \
    Contract: `VG.Spec.Ed25519.scalarReduceContract`. Constant time: only pointers may \
    affect timing."
  safety := [scratchSafety]

def scalarMulAddApi : Api where
  module := "ed25519"
  name := "vg_ed25519_scalar_mul_add"
  sig := scalarMulAddSig
  writeArgs := true
  contracts := some fun A stack => scalarMulAddContract A stack
  summary := "Ed25519 scalar multiply-add (RFC 8032 §5.1.6): writes the canonical 32-byte \
    little-endian encoding of `(r + k*s) mod L` to `*out`. The inputs are unsigned 256-bit \
    little-endian integers; they need not be canonical scalars. \
    Contract: `VG.Spec.Ed25519.scalarMulAddContract`. Constant time: only pointers may \
    affect timing."
  safety := [scratchSafety]

def verifyEquationApi : Api where
  module := "ed25519"
  name := "vg_ed25519_verify_equation"
  sig := verifyEquationSig
  writeArgs := true
  contracts := some fun A stack => verifyEquationContract A stack
  summary := "Checks Ed25519 encodings and the equation `[S]B = R + [k]A` (RFC 8032 §5.1.7), \
    returning 1 if they pass and 0 otherwise. `pk` holds A, `signature` holds R || S, and \
    `challenge` holds all 64 bytes of k as a little-endian integer, used as given: it is \
    not reduced modulo L. To verify a signature on M as RFC 8032 §6 and \
    `VG.Spec.Ed25519.verify` do, the caller must reduce SHA-512(R || A || M) modulo L (e.g. \
    with `vg_ed25519_scalar_reduce`) and supply the 32-byte result followed by 32 zero \
    bytes as `challenge`; this function does not hash M. Passing the unreduced digest \
    instead checks the equation with the full 512-bit k, which RFC 8032 §5.1.7 also \
    permits but which differs from §6 and OpenSSL whenever A has a small-order \
    component. Rejects noncanonical points and S >= L, with no additional subgroup or \
    small-order check. Contract: `VG.Spec.Ed25519.verifyEquationContract`. Not constant \
    time: timing may depend on all inputs."
  safety := [scratchSafety]

def publicKeyApi : Api where
  module := "ed25519"
  name := "vg_ed25519_public_key"
  sig := publicKeySig
  writeArgs := true
  contracts := some fun A stack => publicKeyContract A stack
  summary := "Ed25519 public-key derivation (RFC 8032 §5.1.5): writes the 32-byte public \
    key to `*out`, from the 32-byte private seed at `seed`, including SHA-512 and pruning. \
    Contract: `VG.Spec.Ed25519.publicKeyContract`. Constant time: only pointers may affect \
    timing."
  safety := ["`seed` must originate from a cryptographically secure random generator.", scratchSafety]

def signApi : Api where
  module := "ed25519"
  name := "vg_ed25519_sign"
  sig := signSig
  writeArgs := true
  contracts := some fun A stack => signContract A stack
  summary := "Deterministic Ed25519 signing (RFC 8032 §5.1.6): writes the 64-byte signature \
    to `*out`, for the `len` bytes at `message` and the 32-byte private seed at `seed`. \
    Uses pure Ed25519, with no context or prehash. Derives the public key from the seed. \
    Contract: `VG.Spec.Ed25519.signContract`. Constant time: only pointers and the message \
    length may affect timing, not the seed or message contents."
  safety := ["`seed` must originate from a cryptographically secure random generator.", scratchSafety]

def verifyApi : Api where
  module := "ed25519"
  name := "vg_ed25519_verify"
  sig := verifySig
  writeArgs := true
  contracts := some fun A stack => verifyContract A stack
  summary := "Ed25519 verification (RFC 8032 §5.1.7): returns 1 if the 64-byte signature at \
    `signature` verifies for the 32-byte public key at `pk` and the `len` bytes at \
    `message`, and 0 otherwise. Uses pure Ed25519, with no context or prehash. Checks \
    canonical point encodings, S < L, and `[S]B = R + [k]A` with the challenge \
    k = SHA-512(R || A || M) reduced modulo L, as in RFC 8032 §6. No additional subgroup or small-order check is imposed. \
    Contract: `VG.Spec.Ed25519.verifyContract`. Not constant time: timing may depend on \
    the public key, message and signature."
  safety := [scratchSafety]

end VG.Spec.Ed25519

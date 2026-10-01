import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA-44, ML-DSA-65 and ML-DSA-87: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of ML-DSA's key
generation, signing and verification, for each parameter set `p` of
Table 1, in terms of `Spec/MlDsa.lean`, for any target: `A` is the target's
calling convention. The signatures fix where the arguments are, the memory
each function may access, disjointness, and that the pointers are public
(see `TCB/Sig.lean`); the contracts add the postconditions and what the
functions may leak.

The functions are the internal algorithms of §6, on randomness that the
caller generates (`ML-DSA.KeyGen` and the hedged `ML-DSA.Sign` are these on
fresh random bytes from an approved RBG, §3.6.1), with the message
representative `μ` computed by the caller (which Algorithms 7 and 8 allow:
"may optionally be computed in a different cryptographic module"). A private
key is kept as the 32-byte seed `ξ` it is generated from (§3.6.3):
`vg_mldsa*_keygen` expands it into the public key and the private key,
which is only ever passed to `vg_mldsa*_sign`.

An implementation may bound the loops, as Appendix C allows, by at least
`minBounds` (Table 3) and at most `maxBounds`. So key generation and signing
return 1 with the output of the (unbounded) algorithm of the standard, or 0,
only if a loop does not finish within `minBounds` (which happens with
probability about 2⁻²⁵⁶ or less): their outputs are then unspecified, and
the caller must destroy them and treat the operation as failed (Appendix C).
See `Outcome`. Verification returns 1 only for a valid signature, and 0 for
an invalid one, or if a loop does not finish within `minBounds`.

Everything is secret in key generation and signing but what the contracts
declare they may leak (`Sig.contract`'s `leak`): `ρ`, the seed of the matrix
`Â`, which is part of the public key; in key generation, which half-bytes
`RejBoundedPoly` rejects (`rejBoundedLeak`); and in signing, the number of
iterations of the rejection sampling loop and the commitment hash `c̃` of
each, and the hint of the signature (`signLeak`). Verification's inputs are
all public, and it may leak them. The working space `scratch` holds
intermediate values on return, which the caller must destroy (§3.6.3): room
for the matrix `Â` (`kℓ` polynomials of 1 KiB), `4k + 3ℓ` more polynomials,
and 32 KiB for the rest (`scratchWords`).

The functions may overwrite their arguments passed in memory, where the
calling convention allows it (`writeArgs`), to pass arguments to the
functions they call, and take the number of bytes of stack below the stack
pointer that their calls and frames use (`stack`, see `Sig.contract`),
which depends on the target.
-/

namespace VG.Spec.MlDsa

open Sha3 (bytesAt)

/-- The size of the working space, in `u64`s: 1 KiB (`128` of them) for each
of `kℓ + 4k + 3ℓ + 32` polynomials. -/
def scratchWords (p : Params) : Nat := 128 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)

/-! ## Key generation -/

/-- `(ρ, ρ′, K) ← H(ξ ‖ IntegerToBytes(k, 1) ‖ IntegerToBytes(ℓ, 1), 128)`
(Algorithm 6, line 1). -/
def keyGenSeeds (p : Params) (ξ : List Byte) : List Byte × List Byte × List Byte :=
  let hξ := H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128
  (hξ.take 32, (hξ.drop 32).take 64, (hξ.drop 96).take 32)

/-- What `ML-DSA.KeyGen_internal(ξ)` may leak: `ρ`, and which half-bytes each
`RejBoundedPoly` of `ExpandS(ρ′)` rejects (`rejBoundedLeak`). -/
def keyGenLeak (p : Params) (ξ : List Byte) : List Nat :=
  let (ρ, ρ', _) := keyGenSeeds p ξ
  leakBytes ρ ++ (List.range (p.ℓ + p.k)).flatMap fun r => rejBoundedLeak p.η (ρ' ++ integerToBytes r 2)

/-- `vg_mldsa*_keygen(seed: *const [u8; 32], pk: *mut [u8; pkLen], sk: *mut [u8; skLen], scratch: *mut [u64; scratchWords]) -> u32`.
`seed` holds `ξ`; `scratch` is working space. -/
def keyGenSig (p : Params) : Sig where
  params := [("seed", .array false .u8 32), ("pk", .array true .u8 p.pkLen),
    ("sk", .array true .u8 p.skLen), ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- With the 32 bytes `ξ` at `seed`: writes `ML-DSA.KeyGen_internal(ξ)`
(Algorithm 6) of the parameter set `p` to `pk` and `sk`, and returns 1; or
returns 0 (see `Outcome`). May leak what `keyGenLeak` says. -/
def keyGenContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (keyGenSig p).contract A
    (post := fun seed pk sk _scratch m m' r =>
      Outcome (fun b => keyGenInternal p b (bytesAt m seed 32)) r
        (bytesAt m' pk p.pkLen, bytesAt m' sk p.skLen))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _pk _sk _scratch m => keyGenLeak p (bytesAt m seed 32))

/-! ## Signing -/

/-- What the signing loop may leak (lines 10–32 of Algorithm 7, as
`signLoop`), from the counter `κ`, for at most `iters` more iterations: the
commitment hash `c̃` of each iteration, each followed by how the iteration
ended: 0 if its validity checks rejected it, and 1 then its hint `h` (as 0s
and 1s, which the signature contains) if they passed; nothing if its
`SampleInBall` did not finish. (The tags say where each iteration's leakage
ends: without them, a hint of 0s and 1s would read as the `c̃`s of more
iterations.) -/
def signLeakLoop (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : (iters κ : Nat) → List Nat
  | 0, _ => []
  | iters + 1, κ =>
    leakBytes (signCommit p Â μ ρ'' κ).2.2 ++
      match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
      | some (_, none) => 0 :: signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)
      | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
      | none => []

/-- What `ML-DSA.Sign_internal(sk, M′, rnd)` with the message representative
`μ` (`signMu`) may leak: `ρ`, and the commitment hash `c̃` of each iteration
of the signing loop, whether it was rejected, and the hint of the signature
(`signLeakLoop`), for
loops bounded by `maxBounds`. The number of iterations, and their `c̃`
(pseudorandom outputs of `H` on commitments that are never revealed),
reveal nothing about the private key. -/
def signLeak (p : Params) (sk μ rnd : List Byte) : List Nat :=
  let (ρ, K, _tr, s₁, s₂, t₀) := skDecode p sk
  leakBytes ρ ++
    match expandA p maxBounds ρ with
    | none => []
    | some Â =>
      signLeakLoop p maxBounds Â (s₁.map fun s => ntt (toRq s)) (s₂.map fun s => ntt (toRq s))
        (t₀.map fun t => ntt (toRq t)) μ (H (K ++ rnd ++ μ) 64) maxBounds.sign 0

/-- `vg_mldsa*_sign(sk: *const [u8; skLen], mu: *const [u8; 64], rnd: *const [u8; 32], sig: *mut [u8; sigLen], scratch: *mut [u64; scratchWords]) -> u32`.
`rnd` is the randomness; `scratch` is working space. -/
def signSig (p : Params) : Sig where
  params := [("sk", .array false .u8 p.skLen), ("mu", .array false .u8 64),
    ("rnd", .array false .u8 32), ("sig", .array true .u8 p.sigLen),
    ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- With the private key at `sk`, the message representative `μ` at `mu` and
the 32 bytes of randomness at `rnd`: writes the signature
`ML-DSA.Sign_internal(sk, M′, rnd)` (Algorithm 7) of the parameter set `p`,
for a message `M′` with `H(tr ‖ M′, 64) = μ`, to `sig`, and returns 1; or
returns 0 (see `Outcome`). May leak what `signLeak` says. -/
def signContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeak p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

/-! ## Verification -/

/-- `vg_mldsa*_verify(pk: *const [u8; pkLen], mu: *const [u8; 64], sig: *const [u8; sigLen], scratch: *mut [u64; scratchWords]) -> u32`.
`scratch` is working space. -/
def verifySig (p : Params) : Sig where
  params := [("pk", .array false .u8 p.pkLen), ("mu", .array false .u8 64),
    ("sig", .array false .u8 p.sigLen), ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- With the public key at `pk`, the message representative `μ` at `mu` and
the signature at `sig`: returns 1 if `ML-DSA.Verify_internal(pk, M′, σ)`
(Algorithm 8) of the parameter set `p`, for a message `M′` with
`H(H(pk, 64) ‖ M′, 64) = μ`, is true; and 0 if it is false, or if a loop
does not finish within `minBounds`. May leak its inputs. -/
def verifyContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifySig p).contract A
    (post := fun pk mu sig _scratch m _m' r =>
      let v := fun b => verifyMu p b (bytesAt m pk p.pkLen) (bytesAt m mu 64) (bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun pk mu sig _scratch m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m mu 64 ++ bytesAt m sig p.sigLen))

/-! ## The functions on every target -/

/-- What the documentation says of the return value of a function whose
loops are bounded. -/
private def outcomeDoc : String :=
  "Returns 1 on success. Returns 0 if a loop reaches its bound, which is at least the limit of \
    FIPS 204 Appendix C, Table 3 (this happens with probability about 2^-256 or less): the \
    outputs are then unspecified, and the caller must destroy them and treat the operation as \
    failed."

/-- What the documentation says of the working space. -/
private def scratchSafety : String :=
  "`scratch` is working space: on return it holds intermediate values, which the caller must \
    destroy (FIPS 204 §3.6.3)."

/-- `vg_<module>_keygen` for the parameter set `p` named `name`. -/
def keyGenApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_keygen"
  sig := keyGenSig p
  writeArgs := true
  contracts := some fun A stack => keyGenContract p A stack
  summary := s!"{name} key generation from a seed, `ML-DSA.KeyGen_internal(ξ)` (FIPS 204 \
    Algorithm 6): with the 32-byte seed `ξ` at `seed`, writes the public key to `*pk` and the \
    private key to `*sk`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlDsa.keyGenContract`. Constant time but for `ρ` and rejections: timing \
    may depend on the pointers, on `ρ` (the first 32 bytes of the public key), and on which \
    half-bytes of the SHAKE256 outputs `RejBoundedPoly` rejects (`rejBoundedLeak`, which is \
    independent of the coefficients it samples), but not on anything else of the seed or the \
    keys."
  safety := [
    "`seed` must be random bytes from an approved RBG (FIPS 204 §3.6.1), or a seed so \
      generated before.",
    scratchSafety]

/-- `vg_<module>_sign` for the parameter set `p` named `name`. -/
def signApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_sign"
  sig := signSig p
  writeArgs := true
  contracts := some fun A stack => signContract p A stack
  summary := s!"{name} signing of a message representative, `ML-DSA.Sign_internal(sk, M′, rnd)` \
    (FIPS 204 Algorithm 7) with `μ` computed by the caller: with the private key `*sk`, the \
    64-byte message representative `μ = H(tr ‖ M′, 64)` at `mu` (for the public key hash `tr`, \
    bytes 64–127 of `*sk`) and the randomness `*rnd`, writes the signature to `*sig`. " ++
    outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlDsa.signContract`. Constant time but for `ρ` and the rejection \
    sampling: timing may depend on the pointers, on `ρ` (the first 32 bytes of `*sk`), on the \
    number of iterations of the signing loop and the commitment hash of each, and on the hint \
    of the signature (`signLeak`), but not on anything else of the key, the message \
    representative or the randomness."
  safety := [
    "`sk` must have been written by `" ++ s!"vg_{module}_keygen" ++ "`.",
    "`rnd` must be fresh random bytes (FIPS 204 §3.6.1), or 32 zero bytes for deterministic \
      signing.",
    scratchSafety]

/-- `vg_<module>_verify` for the parameter set `p` named `name`. -/
def verifyApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_verify"
  sig := verifySig p
  writeArgs := true
  contracts := some fun A stack => verifyContract p A stack
  summary := s!"{name} verification of a signature of a message representative, \
    `ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with `μ` computed by the caller: \
    with the public key `*pk`, the 64-byte message representative `μ = H(H(pk, 64) ‖ M′, 64)` \
    at `mu` and the signature `*sig`, returns 1 if the signature is valid, and 0 if it is not \
    or if a loop reaches its bound, which is at least the limit of FIPS 204 Appendix C, \
    Table 3 (this happens with probability about 2^-256 or less).\n\n\
    Contract: `VG.Spec.MlDsa.verifyContract`. Not constant time: timing may depend on the \
    public key, the message representative and the signature."
  safety := [scratchSafety]

/-- `vg_mldsa44_keygen` on every target. -/
def keyGen44Api : Api := keyGenApi mlDsa44 "mldsa44" "ML-DSA-44"
/-- `vg_mldsa44_sign` on every target. -/
def sign44Api : Api := signApi mlDsa44 "mldsa44" "ML-DSA-44"
/-- `vg_mldsa44_verify` on every target. -/
def verify44Api : Api := verifyApi mlDsa44 "mldsa44" "ML-DSA-44"
/-- `vg_mldsa65_keygen` on every target. -/
def keyGen65Api : Api := keyGenApi mlDsa65 "mldsa65" "ML-DSA-65"
/-- `vg_mldsa65_sign` on every target. -/
def sign65Api : Api := signApi mlDsa65 "mldsa65" "ML-DSA-65"
/-- `vg_mldsa65_verify` on every target. -/
def verify65Api : Api := verifyApi mlDsa65 "mldsa65" "ML-DSA-65"
/-- `vg_mldsa87_keygen` on every target. -/
def keyGen87Api : Api := keyGenApi mlDsa87 "mldsa87" "ML-DSA-87"
/-- `vg_mldsa87_sign` on every target. -/
def sign87Api : Api := signApi mlDsa87 "mldsa87" "ML-DSA-87"
/-- `vg_mldsa87_verify` on every target. -/
def verify87Api : Api := verifyApi mlDsa87 "mldsa87" "ML-DSA-87"

end VG.Spec.MlDsa

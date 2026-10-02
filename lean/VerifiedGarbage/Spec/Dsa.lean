import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Sha256

/-!
# DSA — FIPS 186-4 §§4.1–4.7 and Appendices A.1.1.2, A.2.1, B.1.2, B.2.2

**Trusted.** The six operations requested in pyca/verified-garbage#1.
This is the historical finite-field DSA algorithm, not ML-DSA. Integers
are mathematical naturals, digests are already hashed, and signatures are
pairs `(r,s)`; DER encoding and hashing a message are separate layers.

Randomized operations take finite tapes of independent random candidates:
a Rust wrapper must supply OS randomness and retry on exhaustion (`none`).
They must never derive a nonce from a digest or reuse a nonce. This spec
makes no timing claim about its mathematical computations. Exact primality
is intentional; it is not an executable primality-testing implementation.

Parameter generation chooses (1024,160), (2048,256), or (3072,256) for
`generate_parameters(bits)`. Imported (2048,224) parameters are also accepted.
1024-bit DSA is included for legacy interoperability. Seed hashing uses
SHA-1 for N=160 and SHA-256 for N=256. Generator construction is A.2.1's
unverifiable generation, with a separate random h tape (not the verifiable
generator construction). Parameter provenance certificates are not modeled.

`sign` and `verify` require `parametersValid key.params`; `fromComponents`
and `generateParameters` establish it. Their cheap checks additionally
reject invalid scalar ranges, public subgroup membership, and inconsistent
private/public components. This avoids repeating exact primality on every
signature. All digest lengths, including zero, have mathematical meaning;
checking a caller's chosen hash length belongs to a prehash wrapper.
-/

namespace VG.Spec.Dsa

structure Params where
  p : Nat
  q : Nat
  g : Nat
  deriving DecidableEq, Repr

structure Key where
  params : Params
  y : Nat
  x : Option Nat := none
  deriving DecidableEq, Repr

structure Signature where
  r : Nat
  s : Nat
  deriving DecidableEq, Repr

/-- Big-endian unsigned decoding; leading zero bytes are permitted. -/
def decodeBE (bs : List Byte) : Nat := bs.foldl (fun n b => 256 * n + b.toNat) 0

/-- Fixed-width big-endian encoding, modulo 2^(8*n). -/
def encodeBE (n x : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x >>> (8 * (n - 1 - i)))

/-- Square-and-multiply, with reduction at every step. -/
def powMod (a e m : Nat) : Nat :=
  if e = 0 then 1 % m else
    let t := powMod a (e / 2) m
    let u := t * t % m
    if e % 2 = 0 then u else u * a % m
termination_by e
decreasing_by omega

/-- Bit length of an unsigned integer, with bitLength 0 = 0. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- FIPS 186-4 §4.2's (L,N) pairs. -/
def supportedSizes (l n : Nat) : Prop :=
  (l = 1024 ∧ n = 160) ∨ (l = 2048 ∧ (n = 224 ∨ n = 256)) ∨ (l = 3072 ∧ n = 256)

instance (l n : Nat) : Decidable (supportedSizes l n) := by
  unfold supportedSizes
  infer_instance

/-- Exact primality: n ≥ 2 and no divisor strictly between 1 and n.
The finite quantifier makes this decidable using Lean core alone. This is a
mathematical specification, not a practical large-integer primality test. -/
def prime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d : Fin n, 1 < d.val → n % d.val ≠ 0

instance (n : Nat) : Decidable (prime n) := by
  unfold prime
  infer_instance

/-- Full domain validation: prime p,q, q divides p-1, and g has order q. -/
def parametersValid (a : Params) : Prop :=
  supportedSizes (bitLength a.p) (bitLength a.q) ∧ prime a.p ∧ prime a.q ∧
    (a.p - 1) % a.q = 0 ∧ 1 < a.g ∧ a.g < a.p ∧ powMod a.g a.q a.p = 1

instance (a : Params) : Decidable (parametersValid a) := by
  unfold parametersValid
  infer_instance

/-- Public subgroup membership and optional private/public consistency. -/
def keyValid (key : Key) : Bool :=
  let a := key.params
  1 < key.y && key.y < a.p && powMod key.y a.q a.p == 1 &&
    match key.x with
    | none => true
    | some x => 0 < x && x < a.q && powMod a.g x a.p == key.y

/-- Import public (x=none) or private components, with full validation.
No private key is manufactured by silently reducing x modulo q. -/
def fromComponents (p q g y : Nat) (x : Option Nat := none) : Option Key :=
  let key : Key := ⟨⟨p, q, g⟩, y, x⟩
  if parametersValid key.params && keyValid key then some key else none

/-- Export the exact components; public exports have no private scalar. -/
def toComponents (key : Key) : Nat × Nat × Nat × Nat × Option Nat :=
  (key.params.p, key.params.q, key.params.g, key.y, key.x)

/-- §4.6: leftmost min(N,outlen) digest bits, not the digest modulo q.
In particular a short digest is not left-padded by shifting its value. -/
def digestScalar (q : Nat) (digest : List Byte) : Nat :=
  decodeBE digest >>> (8 * digest.length - bitLength q)

/-- B.1.2/B.2.2 equivalent rejection sampling. A candidate has exactly N random bits;
unlike reduction modulo q this does not bias the result. -/
def sampleScalar (q : Nat) (candidates : List Nat) : Option Nat :=
  candidates.find? fun c => 0 < c && c < q

/-- Key generation on validated parameters (§4.4, B.1.2).
Candidates supplied by the wrapper are independent N-bit integers. -/
def generate (a : Params) (candidates : List Nat) : Option Key := do
  let x ← sampleScalar a.q candidates
  return ⟨a, powMod a.g x a.p, some x⟩

/-- One signing attempt with an explicitly supplied ephemeral k (§4.6).
A zero r or s is a retry, never a valid signature. Fermat inversion applies
because the caller has validated that q is prime. -/
def signWithNonce (key : Key) (digest : List Byte) (k : Nat) : Option Signature := do
  let x ← key.x
  if !keyValid key || !(0 < k && k < key.params.q) then none else do
    let a := key.params
    let r := powMod a.g k a.p % a.q
    let s := powMod k (a.q - 2) a.q * (digestScalar a.q digest + x * r) % a.q
    if r == 0 || s == 0 then none else some ⟨r, s⟩

/-- Randomized signing: consume fresh independent N-bit candidates until a
nonzero signature is obtained; exhaustion reports failure. No deterministic
signing or nonce-reuse behavior is specified. -/
def sign (key : Key) (digest : List Byte) : List Nat → Option Signature
  | [] => none
  | k :: ks => match signWithNonce key digest k with
    | some sig => some sig
    | none => sign key digest ks

/-- §4.7: reject out-of-range r,s before inversion. A private key's public
projection can verify too, without consulting x. Validated parameters are a
precondition; the signature and digest need not be trusted. -/
def verify (key : Key) (sig : Signature) (digest : List Byte) : Bool :=
  let a := key.params
  let publicKey := { key with x := none }
  if !keyValid publicKey || !(0 < sig.r && sig.r < a.q && 0 < sig.s && sig.s < a.q) then false
  else
    let w := powMod sig.s (a.q - 2) a.q
    let u1 := digestScalar a.q digest * w % a.q
    let u2 := sig.r * w % a.q
    (powMod a.g u1 a.p * powMod key.y u2 a.p % a.p) % a.q == sig.r

/-- Default subgroup size for the issue's bits-only parameter API. -/
def subgroupBits (bits : Nat) : Option Nat :=
  if bits == 1024 then some 160 else if bits == 2048 || bits == 3072 then some 256 else none

/-- A.1.1.2 seed hash, chosen for the default subgroup size. -/
def seedHash (n : Nat) (seed : List Byte) : List Byte :=
  if n == 160 then Sha1.hash seed else Sha256.hash seed

/-- A.1.1.2 steps 5–6. -/
def qCandidate (n : Nat) (seed : List Byte) : Nat :=
  let u := decodeBE (seedHash n seed) % 2 ^ (n - 1)
  2 ^ (n - 1) + u + 1 - u % 2

/-- A.1.1.2 steps 9–11 at a given offset. Seed addition wraps at seedlen,
and only the high-index hash contribution is truncated to b bits. -/
def pCandidate (l n q : Nat) (seed : List Byte) (offset : Nat) : Nat :=
  let count := (l - 1) / n
  let b := (l - 1) % n
  let w := (List.range (count + 1)).foldl (fun acc j =>
    let v := decodeBE (seedHash n (encodeBE seed.length (decodeBE seed + offset + j)))
    acc + (if j == count then v % 2 ^ b else v) * 2 ^ (j * n)) 0
  let x := w + 2 ^ (l - 1)
  x + 1 - x % (2 * q)

/-- A.1.1.2 step 11 through 4*L attempts. Exact primality specifies the
mathematical result, without prescribing a probabilistic primality tester. -/
def primeFromSeed (l n q : Nat) (seed : List Byte) : Option Nat :=
  ((List.range (4 * l)).map fun counter =>
    pCandidate l n q seed (1 + counter * ((l - 1) / n + 1))).find?
      fun p => decide (2 ^ (l - 1) ≤ p ∧ prime p)

/-- A.2.1 generator search with independent random h candidates. -/
def generator (p q : Nat) (hs : List Nat) : Option Nat :=
  ((hs.filter fun h => 1 < h && h < p - 1).map fun h => powMod h ((p - 1) / q) p).find?
    fun g => 1 < g

/-- Parameter generation from finite randomness tapes. Seeds must have at
least N bits (A.1.1.2 step 3); an exhausted tape or unsupported size fails.
The final validation is an explicit guarantee of the domain invariants. -/
def generateParameters (bits : Nat) (seeds : List (List Byte)) (hs : List Nat) : Option Params := do
  let n ← subgroupBits bits
  let rec attempt : List (List Byte) → Option Params
    | [] => none
    | seed :: rest =>
      if 8 * seed.length < n then attempt rest else
      let q := qCandidate n seed
      if !decide (prime q) then attempt rest else
      match primeFromSeed bits n q seed with
      | some p => match generator p q hs with
        | some g => let a : Params := ⟨p, q, g⟩
                    if parametersValid a then some a else attempt rest
        | none => attempt rest
      | none => attempt rest
  attempt seeds

end VG.Spec.Dsa

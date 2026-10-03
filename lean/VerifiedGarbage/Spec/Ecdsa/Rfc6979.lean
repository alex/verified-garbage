import VerifiedGarbage.Spec.Ecdsa
import VerifiedGarbage.Spec.Hmac

/-!
# Deterministic ECDSA (RFC 6979)

**Trusted** (as every file in `Spec/`). The generation of the per-message
secret number `k` from the private key and the hash, transcribed from
RFC 6979, *Deterministic Usage of the Digital Signature Algorithm (DSA) and
Elliptic Curve Digital Signature Algorithm (ECDSA)* (August 2013), §3.2,
with HMAC over any hash function (`Spec/Hmac.lean`), and the signature
(`Ecdsa.signWith`) with the first suitable candidate.

* `qlen` is the bit length of `n` (`nBits`), `rlen` its length in octets
  (§2.3.2); `hlen` is the length of the hash function's output in octets.
* `bits2int` (§2.3.2) is the integer of the leftmost `qlen` bits, which is
  FIPS 186-5's conversion of the hash (`hashToInt`); `int2octets` (§2.3.3)
  is `rlen` octets, most significant first; `bits2octets` (§2.3.4) is
  `int2octets (bits2int b mod n)`.
* Steps b to g (`init`) derive `K` and `V`; each candidate (step h) is
  `bits2int T` for `T` the concatenation of enough successive
  `V = HMAC_K(V)` to make `qlen` bits (`genT`). A candidate is suitable if
  it is in `[1, n-1]` and gives `r ≠ 0` and `s ≠ 0` (§3.4); otherwise
  `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and step h starts again.

RFC 6979's loop has no bound. `sign` tries at most `tries` candidates and
gives no signature if none is suitable: for a curve whose `n` is close to
`2^qlen`, an unsuitable candidate is rare (for P-256, under `2^-31`), and
`tries` candidates all unsuitable as rare as the instance makes it. It also
gives the number of candidates tried, which an implementation may reveal.
A private key not in `[1, n-1]` gives no signature, and no candidate.
-/

namespace VG.Spec.Ecdsa.Rfc6979

open Weierstrass

variable (C : Curve)

/-- `rlen`, in octets: `qlen` rounded up to whole octets. -/
def rlen : Nat := (nBits C + 7) / 8

/-- `bits2int` (§2.3.2). -/
def bits2int (b : List Byte) : Nat := hashToInt C b

/-- `int2octets` (§2.3.3). -/
def int2octets (x : Nat) : List Byte := toBytes (rlen C) x

/-- `bits2octets` (§2.3.4). -/
def bits2octets (b : List Byte) : List Byte := int2octets C (bits2int C b % C.n)

variable (H : Hmac.HashFunction) (hlen : Nat)

/-- Steps b to g, for the private key `x` and the hash `h1`: `K` and `V`. -/
def init (x : Nat) (h1 : List Byte) : List Byte × List Byte :=
  let m := int2octets C x ++ bits2octets C h1
  let V := List.replicate hlen 1
  let K := List.replicate hlen 0
  let K := Hmac.hmac H K (V ++ 0 :: m)
  let V := Hmac.hmac H K V
  let K := Hmac.hmac H K (V ++ 1 :: m)
  let V := Hmac.hmac H K V
  (K, V)

/-- Steps h.1 and h.2: `T`, the concatenation of `count` successive
`V = HMAC_K(V)`, and the last `V`. -/
def genT (K : List Byte) : Nat → List Byte → List Byte × List Byte
  | 0, V => ([], V)
  | count + 1, V =>
    let V := Hmac.hmac H K V
    let (T, V') := genT K count V
    (V ++ T, V')

/-- Step h.3 after an unsuitable candidate: `K = HMAC_K(V ‖ 0x00)`, then
`V = HMAC_K(V)`. -/
def next (K V : List Byte) : List Byte × List Byte :=
  let K := Hmac.hmac H K (V ++ [0])
  (K, Hmac.hmac H K V)

/-- The number of `V`s in `T`: the least `count` with `8 hlen count ≥ qlen`. -/
def blocks : Nat := (nBits C + 8 * hlen - 1) / (8 * hlen)

/-- Step h with at most `tries` candidates, from `K` and `V`: the signature
of the hash integer `e` with the private key `d` and the first suitable
candidate, and the number of candidates tried. -/
def search (d e : Nat) (K V : List Byte) : Nat → Option (Nat × Nat) × Nat
  | 0 => (none, 0)
  | tries + 1 =>
    let (T, V) := genT H K (blocks C hlen) V
    match signWith C d e (bits2int C T) with
    | some rs => (some rs, 1)
    | none =>
      let (K, V) := next H K V
      let (rs, n) := search d e K V tries
      (rs, n + 1)

/-- The deterministic signature of the hash `h1` with the private key `x`,
trying at most `tries` candidates, and the number of candidates tried: no
signature if `x` is not in `[1, n-1]` or no candidate is suitable. -/
def sign (tries : Nat) (x : Nat) (h1 : List Byte) : Option (Nat × Nat) × Nat :=
  if 1 ≤ x ∧ x < C.n then
    let (K, V) := init C H hlen x h1
    search C H hlen x (hashToInt C h1) K V tries
  else (none, 0)

end VG.Spec.Ecdsa.Rfc6979

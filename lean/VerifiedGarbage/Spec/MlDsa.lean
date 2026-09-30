import VerifiedGarbage.Spec.Sha3

/-!
# ML-DSA (FIPS 204)

**Trusted** (as every file in `Spec/`). The module-lattice-based digital
signature algorithm ML-DSA, transcribed from FIPS 204,
*Module-Lattice-Based Digital Signature Standard* (August 2024); section,
algorithm, table and appendix numbers below refer to it. The algorithms are
written for any parameter set (`Params`), and the three of Table 1 are
`mlDsa44`, `mlDsa65` and `mlDsa87`. HashML-DSA (§5.4) is not specified.

Byte strings are lists of bytes, and bit strings `Array`s of `Bool`s (a bit
`b` is the integer `b.toNat` where the standard does arithmetic with it).
Messages are byte strings: the standard allows any bit string, and this
library signs only whole bytes, as SHAKE256 (`Spec/Sha3.lean`) takes them.
So `BytesToBits(tr) ‖ M′` (Algorithm 7, line 6) is the byte string
`tr ++ M′`. An element of `ℤ_q` is a `Fin q`, whose arithmetic is modulo
`q`; a polynomial of `R_q`, or an element of `T_q` (§2.5), is a `Vector` of
256 of them (`Poly`), coefficient `i` (or entry `i`) at index `i`; and a
polynomial of `R`, with integer coefficients, is a `Vector` of 256 `Int`s
(`IPoly`), cast to `R_q` coefficientwise (`toRq`, §2.4.1) where the
standard uses it as one. A vector of `R_q^k` or `R^k` is a list of `k`
polynomials, and a matrix a list of its rows. A hint of `R_2^k` is a list of
`k` `Vector`s of 256 `Bool`s.

Four algorithms loop an unbounded number of times in the worst case:
`ML-DSA.Sign_internal`'s rejection sampling loop, `RejBoundedPoly`,
`RejNTTPoly` and `SampleInBall`. Appendix C lets an implementation bound
each, by at least the limits of Table 3 (`minBounds`), and fail when a bound
is reached. So the algorithms that use them take `Bounds`: a bound on the
iterations of the signing loop and on the XOF output bytes each of the
others may draw. They return `none` when a loop does not finish within its
bound. The standard's (unbounded) algorithm returns `x` when the bounded one
returns `some x` for some bounds, and larger bounds give the same result.

The hash function and XOFs `H` and `G` are SHAKE256 and SHAKE128
(`Spec/Sha3.lean`, §3.7): squeezing `ℓ` bytes in pieces gives the first
`ℓ` bytes of their output. The contracts of the functions implemented in
assembly are in `Spec/MlDsa/`.
-/

namespace VG.Spec.MlDsa

/-! ## Constants and parameter sets (§2.3, §4) -/

/-- `n = 256`, the degree of the polynomials of `R` and `R_q`. -/
abbrev n : Nat := 256

/-- The prime `q = 8380417 = 2²³ - 2¹³ + 1` (Table 1). -/
abbrev q : Nat := 8380417

/-- `ℤ_q`: arithmetic on `Fin q` is modulo `q` (§2.4.1). An element is the
integer in `{0, …, q - 1}` that represents it (`.val`, which is
`r mod q`). -/
abbrev Zq := Fin q

/-- An element of `R_q` (its coefficients, `w[i] = wᵢ`) or of `T_q` (§2.5). -/
abbrev Poly := Vector Zq n

/-- An element of `R`: a polynomial with integer coefficients. -/
abbrev IPoly := Vector Int n

/-- The integer `x mod q` as an element of `ℤ_q` (§2.4.1). -/
def ofInt (x : Int) : Zq := Fin.ofNat q (x % (q : Int)).toNat

/-- A polynomial of `R` as one of `R_q`, coefficientwise (§2.4.1). -/
def toRq (w : IPoly) : Poly := w.map ofInt

/-- `d = 13`, the number of bits dropped from `t` (Table 1). -/
abbrev d : Nat := 13

/-- `ζ = 1753`, a 512th root of unity in `ℤ_q` (Table 1, §2.5). -/
def ζ : Zq := 1753

/-- `bitlen a`, for a positive integer `a`: the number of digits of its
base-2 representation (§2.3), e.g. `bitlen 32 = 6` and `bitlen 31 = 5`. -/
def bitlen (a : Nat) : Nat := Nat.log2 a + 1

/-- A parameter set (Table 1): the dimensions `(k, ℓ)` of `A`, the private key
range `η`, the number `τ` of `±1`s in `c`, the collision strength `λ` of `c̃`
(`lam`, as `λ` is Lean syntax), the coefficient range `γ₁` of `y`, the
low-order rounding range `γ₂`, and the largest number `ω` of 1s in the hint
`h`. -/
structure Params where
  k : Nat
  ℓ : Nat
  η : Nat
  τ : Nat
  lam : Nat
  γ₁ : Nat
  γ₂ : Nat
  ω : Nat

/-- ML-DSA-44 (Table 1): `(k, ℓ) = (4, 4)`, `η = 2`, `τ = 39`, `λ = 128`,
`γ₁ = 2¹⁷`, `γ₂ = (q - 1)/88`, `ω = 80`. -/
def mlDsa44 : Params :=
  { k := 4, ℓ := 4, η := 2, τ := 39, lam := 128, γ₁ := 2 ^ 17, γ₂ := (q - 1) / 88, ω := 80 }

/-- ML-DSA-65 (Table 1): `(k, ℓ) = (6, 5)`, `η = 4`, `τ = 49`, `λ = 192`,
`γ₁ = 2¹⁹`, `γ₂ = (q - 1)/32`, `ω = 55`. -/
def mlDsa65 : Params :=
  { k := 6, ℓ := 5, η := 4, τ := 49, lam := 192, γ₁ := 2 ^ 19, γ₂ := (q - 1) / 32, ω := 55 }

/-- ML-DSA-87 (Table 1): `(k, ℓ) = (8, 7)`, `η = 2`, `τ = 60`, `λ = 256`,
`γ₁ = 2¹⁹`, `γ₂ = (q - 1)/32`, `ω = 75`. -/
def mlDsa87 : Params :=
  { k := 8, ℓ := 7, η := 2, τ := 60, lam := 256, γ₁ := 2 ^ 19, γ₂ := (q - 1) / 32, ω := 75 }

/-- `β = τ · η` (Table 1). -/
def Params.β (p : Params) : Nat := p.τ * p.η

/-- The length of the commitment hash `c̃`, `λ/4` bytes (Algorithm 7,
line 15). -/
def Params.ctildeLen (p : Params) : Nat := p.lam / 4

/-- The length of a public key, `32 + 32k(bitlen (q - 1) - d)` bytes
(Algorithm 22). -/
def Params.pkLen (p : Params) : Nat := 32 + 32 * p.k * (bitlen (q - 1) - d)

/-- The length of a private key, `32 + 32 + 64 + 32((ℓ + k) bitlen (2η) + dk)`
bytes (Algorithm 24). -/
def Params.skLen (p : Params) : Nat :=
  32 + 32 + 64 + 32 * ((p.ℓ + p.k) * bitlen (2 * p.η) + d * p.k)

/-- The length of a signature, `λ/4 + ℓ · 32 (1 + bitlen (γ₁ - 1)) + ω + k`
bytes (Algorithm 26). -/
def Params.sigLen (p : Params) : Nat :=
  p.ctildeLen + p.ℓ * 32 * (1 + bitlen (p.γ₁ - 1)) + p.ω + p.k

/-- Bounds on the loops of Appendix C: on the iterations of the rejection
sampling loop of `ML-DSA.Sign_internal` (`sign`), and on the XOF output
bytes that `RejBoundedPoly`, `RejNTTPoly` and `SampleInBall` draw
(`rejBounded`, `rejNTT` and `ball`). -/
structure Bounds where
  sign : Nat
  rejBounded : Nat
  rejNTT : Nat
  ball : Nat

/-- The least bounds an implementation may put on the loops (Appendix C,
Table 3): 814 iterations of the signing loop, and 481, 894 and 221 bytes of
XOF output for `RejBoundedPoly`, `RejNTTPoly` and `SampleInBall`. -/
def minBounds : Bounds := { sign := 814, rejBounded := 481, rejNTT := 894, ball := 221 }

/-! ## Cryptographic functions (§3.7) -/

/-- `H(s, ℓ)`: the first `ℓ` bytes of SHAKE256 of `s` (§3.7). -/
def H (s : List Byte) (ℓ : Nat) : List Byte := Sha3.shake256 s ℓ

/-- `G(s, ℓ)`: the first `ℓ` bytes of SHAKE128 of `s` (§3.7). -/
def G (s : List Byte) (ℓ : Nat) : List Byte := Sha3.shake128 s ℓ

/-! ## Modular reduction and norms (§2.3) -/

/-- `m mod± α`, for a positive integer `α`: the unique `m′` with
`-⌈α/2⌉ < m′ ≤ ⌊α/2⌋` congruent to `m` modulo `α` (§2.3). -/
def modPm (m : Int) (α : Nat) : Int :=
  let r := m % (α : Int)
  if r > (α / 2 : Nat) then r - α else r

/-- `‖w‖∞` for `w ∈ ℤ_q`: `|w mod± q|` (§2.3). -/
def normZq (w : Zq) : Nat := (modPm w.val q).natAbs

/-- `‖w‖∞` for a vector of `R_q^m`: the largest `‖wᵢ‖∞` of the coefficients
`wᵢ` of its polynomials, 0 for none (§2.3). -/
def normRq (v : List Poly) : Nat := (v.flatMap fun w => w.toList.map normZq).foldl max 0

/-- `‖w‖∞` for a vector of `R^m`: the largest `|wᵢ|` of the coefficients
`wᵢ` of its polynomials, 0 for none (§2.3). -/
def normR (v : List IPoly) : Nat := (v.flatMap fun w => w.toList.map Int.natAbs).foldl max 0

/-! ## Conversion between data types (§7.1) -/

/-- Algorithm 9, `IntegerToBits(x, α)`: `y[i]` is `x′ mod 2` after `i`
halvings `x′ ← ⌊x′/2⌋` of `x′ = x`, i.e. `⌊x/2ⁱ⌋ mod 2`, for `i < α`. -/
def integerToBits (x α : Nat) : List Bool := (List.range α).map fun i => decide (x / 2 ^ i % 2 = 1)

/-- Algorithm 10, `BitsToInteger(y, α)`, for the `α` bits `y`: `x ← 2x + y[α - i]`
for `i` from 1 to `α`, i.e. `∑ᵢ y[i] · 2ⁱ`. -/
def bitsToInteger (y : List Bool) : Nat := y.foldr (fun b x => 2 * x + b.toNat) 0

/-- Algorithm 11, `IntegerToBytes(x, α)`: `y[i]` is `x′ mod 256` after `i`
steps `x′ ← ⌊x′/256⌋` of `x′ = x`, i.e. `⌊x/256ⁱ⌋ mod 256`, for `i < α`. -/
def integerToBytes (x α : Nat) : List Byte := (List.range α).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

/-- Algorithm 12, `BitsToBytes(y)`, for a bit string `y` of length `α`: the
`⌈α/8⌉` bytes `z` with `z[⌊i/8⌋] ← z[⌊i/8⌋] + y[i] · 2^(i mod 8)` for each
`i < α`. -/
def bitsToBytes (y : Array Bool) : List Byte :=
  (List.range ((y.size + 7) / 8)).map fun i =>
    BitVec.ofNat 8 ((List.range 8).map fun j => (y.getD (8 * i + j) false).toNat * 2 ^ j).sum

/-- Algorithm 13, `BytesToBits(z)`: `y[8i + j]` is `z′[i] mod 2` after `j`
halvings `z′[i] ← ⌊z′[i]/2⌋` of `z′[i] = z[i]`, i.e. `⌊z[i]/2ʲ⌋ mod 2`. -/
def bytesToBits (z : List Byte) : Array Bool :=
  (z.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)).toArray

/-- Algorithm 14, `CoeffFromThreeBytes(b₀, b₁, b₂)`: `z = 2¹⁶ · b₂′ + 2⁸ · b₁ + b₀`,
with `b₂′` the byte `b₂` with its top bit set to zero, if `z < q`, and `⊥`
(`none`) otherwise. -/
def coeffFromThreeBytes (b₀ b₁ b₂ : Byte) : Option Zq :=
  let b₂' := if b₂.toNat > 127 then b₂.toNat - 128 else b₂.toNat
  let z := 2 ^ 16 * b₂' + 2 ^ 8 * b₁.toNat + b₀.toNat
  if h : z < q then some ⟨z, h⟩ else none

/-- Algorithm 15, `CoeffFromHalfByte(b)`, for `η ∈ {2, 4}` and `b < 16`:
`2 - (b mod 5)` if `η = 2` and `b < 15`, `4 - b` if `η = 4` and `b < 9`, and
`⊥` (`none`) otherwise. -/
def coeffFromHalfByte (η b : Nat) : Option Int :=
  if η = 2 ∧ b < 15 then some (2 - (b % 5 : Nat))
  else if η = 4 ∧ b < 9 then some (4 - b)
  else none

/-- Algorithm 16, `SimpleBitPack(w, b)`, for `w` with coefficients in
`[0, b]`: `BitsToBytes` of the `IntegerToBits(wᵢ, bitlen b)` of the
coefficients, concatenated; `32 · bitlen b` bytes. -/
def simpleBitPack (w : Vector Nat n) (b : Nat) : List Byte :=
  bitsToBytes (w.toList.flatMap fun wi => integerToBits wi (bitlen b)).toArray

/-- Algorithm 17, `BitPack(w, a, b)`, for `w` with coefficients in `[-a, b]`:
`BitsToBytes` of the `IntegerToBits(b - wᵢ, bitlen (a + b))` of the
coefficients, concatenated; `32 · bitlen (a + b)` bytes. -/
def bitPack (w : IPoly) (a b : Nat) : List Byte :=
  bitsToBytes (w.toList.flatMap fun wi => integerToBits ((b : Int) - wi).toNat (bitlen (a + b))).toArray

/-- Algorithm 18, `SimpleBitUnpack(v, b)`, for `v` of `32 · bitlen b` bytes:
`wᵢ ← BitsToInteger((z[ic], …, z[ic + c - 1]), c)` for `c = bitlen b` and
`z ← BytesToBits(v)`. -/
def simpleBitUnpack (v : List Byte) (b : Nat) : Vector Nat n :=
  let c := bitlen b
  let z := bytesToBits v
  Vector.ofFn fun i => bitsToInteger ((List.range c).map fun j => z.getD (i.val * c + j) false)

/-- Algorithm 19, `BitUnpack(v, a, b)`, for `v` of `32 · bitlen (a + b)`
bytes: `wᵢ ← b - BitsToInteger((z[ic], …, z[ic + c - 1]), c)` for
`c = bitlen (a + b)` and `z ← BytesToBits(v)`. -/
def bitUnpack (v : List Byte) (a b : Nat) : IPoly :=
  let c := bitlen (a + b)
  let z := bytesToBits v
  Vector.ofFn fun i =>
    (b : Int) - bitsToInteger ((List.range c).map fun j => z.getD (i.val * c + j) false)

/-- Algorithm 20, `HintBitPack(h)`, for a hint `h` of `R_2^k` with at most
`ω` nonzero coefficients in all: the `ω + k` bytes `y`, whose first bytes
are the indices `j` of the nonzero coefficients `h[i]ⱼ`, in order of `i`
then `j`, and zeros after them, and whose byte `ω + i` is the number of
nonzero coefficients in `h[0], …, h[i]`. -/
def hintBitPack (ω k : Nat) (h : List (Vector Bool n)) : List Byte := Id.run do
  let mut y : Array Byte := Array.replicate (ω + k) 0
  let mut index := 0
  for i in List.range k do
    for j in List.range n do
      if (h.getD i (Vector.replicate n false))[j]! then
        y := y.set! index (BitVec.ofNat 8 j)
        index := index + 1
    y := y.set! (ω + i) (BitVec.ofNat 8 index)
  return y.toList

/-- Algorithm 21, `HintBitUnpack(y)`, for `y` of `ω + k` bytes: the hint `h`
that `HintBitPack` encodes as `y`, or `⊥` (`none`) if `y` is malformed: a
count `y[ω + i]` less than the previous one or greater than `ω`, indices of
one polynomial not strictly increasing, or a nonzero byte after the last
index. -/
def hintBitUnpack (ω k : Nat) (y : List Byte) : Option (List (Vector Bool n)) := Id.run do
  let y := y.toArray
  let mut h : Array (Vector Bool n) := Array.replicate k (Vector.replicate n false)
  let mut index := 0
  for i in List.range k do
    let bound := (y.getD (ω + i) 0).toNat
    if bound < index ∨ bound > ω then return none
    let first := index
    -- `while Index < y[ω + i]`: `y[ω + i] - Index` iterations.
    for _ in List.range (bound - index) do
      if index > first then
        if (y.getD (index - 1) 0).toNat ≥ (y.getD index 0).toNat then return none
      h := h.set! i ((h.getD i (Vector.replicate n false)).set! (y.getD index 0).toNat true)
      index := index + 1
  for i in List.range' index (ω - index) do
    if y.getD i 0 ≠ 0 then return none
  return some h.toList

/-! ## Encodings of keys and signatures (§7.2) -/

/-- `2^(bitlen (q - 1) - d) - 1`, the bound on the coefficients of `t₁`
(Algorithm 22). -/
def t1Max : Nat := 2 ^ (bitlen (q - 1) - d) - 1

/-- Algorithm 22, `pkEncode(ρ, t₁)`: `ρ` followed by the
`SimpleBitPack(t₁[i], 2^(bitlen (q - 1) - d) - 1)`. -/
def pkEncode (ρ : List Byte) (t₁ : List (Vector Nat n)) : List Byte :=
  ρ ++ t₁.flatMap fun t => simpleBitPack t t1Max

/-- Algorithm 23, `pkDecode(pk)`: `ρ = pk[0 : 32]`, and `t₁[i]` the
`SimpleBitUnpack` of the following `k` pieces of `32(bitlen (q - 1) - d)`
bytes. -/
def pkDecode (p : Params) (pk : List Byte) : List Byte × List (Vector Nat n) :=
  let len := 32 * (bitlen (q - 1) - d)
  (pk.take 32, (List.range p.k).map fun i => simpleBitUnpack ((pk.drop (32 + len * i)).take len) t1Max)

/-- Algorithm 24, `skEncode(ρ, K, tr, s₁, s₂, t₀)`: `ρ ‖ K ‖ tr`, then the
`BitPack(s₁[i], η, η)`, the `BitPack(s₂[i], η, η)` and the
`BitPack(t₀[i], 2^(d-1) - 1, 2^(d-1))`. -/
def skEncode (p : Params) (ρ K tr : List Byte) (s₁ s₂ t₀ : List IPoly) : List Byte :=
  ρ ++ K ++ tr ++ s₁.flatMap (bitPack · p.η p.η) ++ s₂.flatMap (bitPack · p.η p.η) ++
    t₀.flatMap (bitPack · (2 ^ (d - 1) - 1) (2 ^ (d - 1)))

/-- The pieces `B[o + len · i : o + len · (i + 1)]` of `B`, for `i < m`. -/
def pieces (B : List Byte) (o len m : Nat) : List (List Byte) :=
  (List.range m).map fun i => (B.drop (o + len * i)).take len

/-- Algorithm 25, `skDecode(sk)`: `ρ`, `K` and `tr` (the first 32, 32 and 64
bytes), and `s₁`, `s₂` and `t₀`, the `BitUnpack`s of the following `ℓ`, `k`
and `k` pieces of `32 · bitlen (2η)`, `32 · bitlen (2η)` and `32d` bytes.
(`s₁` and `s₂` may lie outside `[-η, η]` if `sk` is malformed.) -/
def skDecode (p : Params) (sk : List Byte) :
    List Byte × List Byte × List Byte × List IPoly × List IPoly × List IPoly :=
  let lenS := 32 * bitlen (2 * p.η)
  let oS₂ := 128 + lenS * p.ℓ
  let oT₀ := oS₂ + lenS * p.k
  (sk.take 32, (sk.drop 32).take 32, (sk.drop 64).take 64,
    (pieces sk 128 lenS p.ℓ).map (bitUnpack · p.η p.η),
    (pieces sk oS₂ lenS p.k).map (bitUnpack · p.η p.η),
    (pieces sk oT₀ (32 * d) p.k).map (bitUnpack · (2 ^ (d - 1) - 1) (2 ^ (d - 1))))

/-- Algorithm 26, `sigEncode(c̃, z, h)`: `c̃`, then the `BitPack(z[i], γ₁ - 1, γ₁)`,
then `HintBitPack(h)`. -/
def sigEncode (p : Params) (ctilde : List Byte) (z : List IPoly) (h : List (Vector Bool n)) :
    List Byte :=
  ctilde ++ z.flatMap (bitPack · (p.γ₁ - 1) p.γ₁) ++ hintBitPack p.ω p.k h

/-- Algorithm 27, `sigDecode(σ)`: `c̃` (the first `λ/4` bytes), `z[i]` the
`BitUnpack(xᵢ, γ₁ - 1, γ₁)` of the following `ℓ` pieces `xᵢ` of
`32(1 + bitlen (γ₁ - 1))` bytes, and `h ← HintBitUnpack(y)` of the last
`ω + k` bytes `y`, which is `⊥` (`none`) if they are malformed. -/
def sigDecode (p : Params) (σ : List Byte) :
    List Byte × List IPoly × Option (List (Vector Bool n)) :=
  let lenZ := 32 * (1 + bitlen (p.γ₁ - 1))
  (σ.take p.ctildeLen,
    (pieces σ p.ctildeLen lenZ p.ℓ).map (bitUnpack · (p.γ₁ - 1) p.γ₁),
    hintBitUnpack p.ω p.k ((σ.drop (p.ctildeLen + lenZ * p.ℓ)).take (p.ω + p.k)))

/-- Algorithm 28, `w1Encode(w₁)`: the `SimpleBitPack(w₁[i], (q - 1)/(2γ₂) - 1)`,
concatenated. -/
def w1Encode (p : Params) (w₁ : List (Vector Nat n)) : List Byte :=
  w₁.flatMap fun w => simpleBitPack w ((q - 1) / (2 * p.γ₂) - 1)

/-! ## Pseudorandom sampling (§7.3) -/

/-- Lines 6–13 of Algorithm 29, `SampleInBall`, from index `i` on, with `c`
so far, the sign bits `h` and the bytes `out` still to squeeze from `H`:
`some c` once `i = 256`, and `none` if `out` runs out first. Each byte `j`
greater than `i` is rejected (line 8); otherwise `cᵢ ← cⱼ` and
`cⱼ ← (-1)^h[i + τ - 256]`. -/
def ballLoop (τ : Nat) (h : Array Bool) : IPoly → Nat → List Byte → Option IPoly
  | c, i, [] => if i ≥ n then some c else none
  | c, i, j :: out =>
    if i ≥ n then some c
    else if j.toNat > i then ballLoop τ h c i out
    else
      ballLoop τ h ((c.set! i c[j.toNat]!).set! j.toNat (if h.getD (i + τ - 256) false then -1 else 1))
        (i + 1) out

/-- Algorithm 29, `SampleInBall(ρ)`, for `τ ≤ 64`, drawing at most `bound` bytes of output
from `H` (Appendix C): the first 8 give the sign bits `h ← BytesToBits(s)`,
and the following ones the indices; `none` if they run out. -/
def sampleInBall (τ bound : Nat) (ρ : List Byte) : Option IPoly :=
  let out := H ρ bound
  if out.length < 8 then none else
  ballLoop τ (bytesToBits (out.take 8)) (Vector.replicate n 0) (256 - τ) (out.drop 8)

/-- Lines 4–10 of Algorithm 30, `RejNTTPoly`, from the coefficients `a`
sampled so far (`j = |a|`), taking the 3-byte arrays `s` of the loop's
iterations from the XOF output `out`: `some a` once `j = 256`, and `none` if
`out` runs out first. -/
def rejNTTLoop : List Zq → List Byte → Option (List Zq)
  | a, s₀ :: s₁ :: s₂ :: out =>
    if a.length ≥ n then some a
    else rejNTTLoop (match coeffFromThreeBytes s₀ s₁ s₂ with
      | some c => a ++ [c]
      | none => a) out
  | a, _ => if a.length ≥ n then some a else none

/-- Algorithm 30, `RejNTTPoly(ρ)`, for a 34-byte `ρ`, drawing at most `bound`
bytes of output from `G` (Appendix C); `none` if it does not finish within
them. -/
def rejNTTPoly (bound : Nat) (ρ : List Byte) : Option Poly :=
  (rejNTTLoop [] (G ρ bound)).map fun a => Vector.ofFn fun i => a.getD i.val 0

/-- Lines 4–16 of Algorithm 31, `RejBoundedPoly`, from the coefficients `a`
sampled so far (`j = |a|`), taking the byte `z` of each iteration from the
XOF output `out`: `some a` once `j = 256`, and `none` if `out` runs out
first. -/
def rejBoundedLoop (η : Nat) : List Int → List Byte → Option (List Int)
  | a, [] => if a.length ≥ n then some a else none
  | a, z :: out =>
    if a.length ≥ n then some a
    else
      let a := match coeffFromHalfByte η (z.toNat % 16) with
        | some z₀ => a ++ [z₀]
        | none => a
      let a := match coeffFromHalfByte η (z.toNat / 16) with
        | some z₁ => if a.length < n then a ++ [z₁] else a
        | none => a
      rejBoundedLoop η a out

/-- Algorithm 31, `RejBoundedPoly(ρ)`, for a 66-byte `ρ`, drawing at most
`bound` bytes of output from `H` (Appendix C); `none` if it does not finish
within them. -/
def rejBoundedPoly (η bound : Nat) (ρ : List Byte) : Option IPoly :=
  (rejBoundedLoop η [] (H ρ bound)).map fun a => Vector.ofFn fun i => a.getD i.val 0

/-- Algorithm 32, `ExpandA(ρ)`: the `k × ℓ` matrix `Â` with
`Â[r, s] ← RejNTTPoly(ρ ‖ IntegerToBytes(s, 1) ‖ IntegerToBytes(r, 1))`, as
its rows; `none` if a `RejNTTPoly` does not finish within `b.rejNTT` bytes. -/
def expandA (p : Params) (b : Bounds) (ρ : List Byte) : Option (List (List Poly)) :=
  (List.range p.k).mapM fun r => (List.range p.ℓ).mapM fun s =>
    rejNTTPoly b.rejNTT (ρ ++ integerToBytes s 1 ++ integerToBytes r 1)

/-- Algorithm 33, `ExpandS(ρ)`: `s₁[r] ← RejBoundedPoly(ρ ‖ IntegerToBytes(r, 2))`
for `r < ℓ` and `s₂[r] ← RejBoundedPoly(ρ ‖ IntegerToBytes(r + ℓ, 2))` for
`r < k`; `none` if a `RejBoundedPoly` does not finish within `b.rejBounded`
bytes. -/
def expandS (p : Params) (b : Bounds) (ρ : List Byte) : Option (List IPoly × List IPoly) := do
  let s₁ ← (List.range p.ℓ).mapM fun r =>
    rejBoundedPoly p.η b.rejBounded (ρ ++ integerToBytes r 2)
  let s₂ ← (List.range p.k).mapM fun r =>
    rejBoundedPoly p.η b.rejBounded (ρ ++ integerToBytes (r + p.ℓ) 2)
  return (s₁, s₂)

/-- Algorithm 34, `ExpandMask(ρ, μ)`: `y[r] ← BitUnpack(H(ρ ‖ IntegerToBytes(μ + r, 2), 32c), γ₁ - 1, γ₁)`
for `r < ℓ`, with `c = 1 + bitlen (γ₁ - 1)`. -/
def expandMask (p : Params) (ρ : List Byte) (μ : Nat) : List IPoly :=
  let c := 1 + bitlen (p.γ₁ - 1)
  (List.range p.ℓ).map fun r => bitUnpack (H (ρ ++ integerToBytes (μ + r) 2) (32 * c)) (p.γ₁ - 1) p.γ₁

/-! ## High-order and low-order bits and hints (§7.4) -/

/-- Algorithm 35, `Power2Round(r)`: `r₀ = r⁺ mod± 2ᵈ` and `r₁ = (r⁺ - r₀)/2ᵈ`,
for `r⁺ = r mod q`. -/
def power2Round (r : Zq) : Int × Int :=
  let r₀ := modPm r.val (2 ^ d)
  ((r.val - r₀) / 2 ^ d, r₀)

/-- Algorithm 36, `Decompose(r)`: `r₀ = r⁺ mod± (2γ₂)` for `r⁺ = r mod q`,
and `r₁ = (r⁺ - r₀)/(2γ₂)`; but `(0, r₀ - 1)` if `r⁺ - r₀ = q - 1`. -/
def decompose (γ₂ : Nat) (r : Zq) : Int × Int :=
  let r₀ := modPm r.val (2 * γ₂)
  if (r.val : Int) - r₀ = q - 1 then (0, r₀ - 1)
  else ((r.val - r₀) / (2 * γ₂ : Nat), r₀)

/-- Algorithm 37, `HighBits(r)`: `r₁` of `Decompose(r)`. -/
def highBits (γ₂ : Nat) (r : Zq) : Int := (decompose γ₂ r).1

/-- Algorithm 38, `LowBits(r)`: `r₀` of `Decompose(r)`. -/
def lowBits (γ₂ : Nat) (r : Zq) : Int := (decompose γ₂ r).2

/-- Algorithm 39, `MakeHint(z, r)`: whether `HighBits(r) ≠ HighBits(r + z)`. -/
def makeHint (γ₂ : Nat) (z r : Zq) : Bool := highBits γ₂ r ≠ highBits γ₂ (r + z)

/-- Algorithm 40, `UseHint(h, r)`: for `m = (q - 1)/(2γ₂)` and
`(r₁, r₀) = Decompose(r)`, `(r₁ + 1) mod m` if `h` and `r₀ > 0`,
`(r₁ - 1) mod m` if `h` and `r₀ ≤ 0`, and `r₁` otherwise. -/
def useHint (γ₂ : Nat) (h : Bool) (r : Zq) : Int :=
  let m := (q - 1) / (2 * γ₂)
  let (r₁, r₀) := decompose γ₂ r
  if h ∧ r₀ > 0 then (r₁ + 1) % (m : Int)
  else if h ∧ r₀ ≤ 0 then (r₁ - 1) % (m : Int)
  else r₁

/-! ## NTT and NTT⁻¹ (§7.5) -/

/-- Algorithm 43, `BitRev8(m)`: `m₇ + 2m₆ + 4m₅ + ⋯ + 128m₀` for
`m = m₀ + 2m₁ + ⋯ + 128m₇`. -/
def bitRev8 (m : Nat) : Nat := ((List.range 8).map fun i => m / 2 ^ i % 2 * 2 ^ (7 - i)).sum

/-- `zetas[m] = ζ^BitRev8(m) mod q` (§7.5, Appendix B). -/
def zetas (m : Nat) : Zq := ζ ^ bitRev8 m

/-- Algorithm 41, `NTT(w)`. -/
def ntt (w : Poly) : Poly := Id.run do
  let mut w := w
  let mut m := 0
  -- while (len ≥ 1), len ← 128, then ⌊len/2⌋
  for len in [128, 64, 32, 16, 8, 4, 2, 1] do
    -- while (start < 256), start ← 0, then start + 2·len
    for start in List.range' 0 (n / (2 * len)) (2 * len) do
      m := m + 1
      let z := zetas m
      for j in List.range' start len do
        let t := z * w[j + len]!
        w := w.set! (j + len) (w[j]! - t)
        w := w.set! j (w[j]! + t)
  return w

/-- Algorithm 42, `NTT⁻¹(ŵ)`. -/
def nttInv (w : Poly) : Poly := Id.run do
  let mut w := w
  let mut m := 256
  -- while (len < 256), len ← 1, then 2·len
  for len in [1, 2, 4, 8, 16, 32, 64, 128] do
    -- while (start < 256), start ← 0, then start + 2·len
    for start in List.range' 0 (n / (2 * len)) (2 * len) do
      m := m - 1
      let z := -zetas m
      for j in List.range' start len do
        let t := w[j]!
        w := w.set! j (t + w[j + len]!)
        w := w.set! (j + len) (t - w[j + len]!)
        w := w.set! (j + len) (z * w[j + len]!)
  -- multiply every coefficient by f = 8347681 = 256⁻¹ mod q
  return w.map (· * 8347681)

/-! ## Arithmetic under NTT (§7.6) -/

/-- Algorithm 44, `AddNTT(â, b̂)`, and addition in `R_q` (both are
coefficientwise). -/
def add (a b : Poly) : Poly := Vector.zipWith (· + ·) a b

/-- Subtraction in `T_q` or `R_q`, coefficientwise. -/
def sub (a b : Poly) : Poly := Vector.zipWith (· - ·) a b

/-- Negation in `R_q`, coefficientwise. -/
def neg (a : Poly) : Poly := a.map (- ·)

/-- Algorithm 45, `MultiplyNTT(â, b̂)`: `ĉ[i] ← â[i] · b̂[i]`. -/
def multiplyNTT (a b : Poly) : Poly := Vector.zipWith (· * ·) a b

/-- Algorithm 46, `AddVectorNTT(v̂, ŵ)`, and the sum of vectors of `R_q^m`. -/
def addVec (v w : List Poly) : List Poly := List.zipWith add v w

/-- The difference of vectors of `T_q^m` or `R_q^m`. -/
def subVec (v w : List Poly) : List Poly := List.zipWith sub v w

/-- Algorithm 47, `ScalarVectorNTT(ĉ, v̂)`: `ŵ[i] ← MultiplyNTT(ĉ, v̂[i])`. -/
def scalarVectorNTT (c : Poly) (v : List Poly) : List Poly := v.map (multiplyNTT c)

/-- The zero of `T_q`. -/
def zero : Poly := Vector.replicate n 0

/-- Algorithm 48, `MatrixVectorNTT(M̂, v̂)`: entry `i` is
`∑_j MultiplyNTT(M̂[i, j], v̂[j])`, summed from `j = 0` with `AddNTT`. -/
def matrixVectorNTT (M : List (List Poly)) (v : List Poly) : List Poly :=
  M.map fun row => (List.zipWith multiplyNTT row v).foldl add zero

/-! ## ML-DSA key generation, signing and verification (§6) -/

/-- Algorithm 6, `ML-DSA.KeyGen_internal(ξ)`: the public key `pk` and the
private key `sk`; `none` if a `RejNTTPoly` or `RejBoundedPoly` does not finish
within its bound. -/
def keyGenInternal (p : Params) (b : Bounds) (ξ : List Byte) :
    Option (List Byte × List Byte) := do
  let hξ := H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128
  let ρ := hξ.take 32
  let ρ' := (hξ.drop 32).take 64
  let K := (hξ.drop 96).take 32
  let Â ← expandA p b ρ
  let (s₁, s₂) ← expandS p b ρ'
  let ŝ₁ := s₁.map fun s => ntt (toRq s)
  let t := addVec ((matrixVectorNTT Â ŝ₁).map nttInv) (s₂.map toRq)
  let t₁ := t.map fun ti => ti.map fun c => (power2Round c).1.toNat
  let t₀ := t.map fun ti => ti.map fun c => (power2Round c).2
  let pk := pkEncode ρ t₁
  let tr := H pk 64
  let sk := skEncode p ρ K tr s₁ s₂ t₀
  return (pk, sk)

/-- The public key hash `tr` in a private key: `sk[64 : 128]` (Algorithm 25). -/
def skTr (sk : List Byte) : List Byte := (sk.drop 64).take 64

/-- The message representative `μ ← H(BytesToBits(tr) ‖ M′, 64)` (Algorithm 7,
line 6, and Algorithm 8, line 7). -/
def messageRep (tr M' : List Byte) : List Byte := H (tr ++ M') 64

/-- Lines 11–15 of Algorithm 7: the mask `y ← ExpandMask(ρ″, κ)`, the
`w ← NTT⁻¹(Â ∘ NTT(y))` and the commitment hash
`c̃ ← H(μ ‖ w1Encode(HighBits(w)), λ/4)` of the iteration of the signing loop
with counter `κ`. -/
def signCommit (p : Params) (Â : List (List Poly)) (μ ρ'' : List Byte) (κ : Nat) :
    List IPoly × List Poly × List Byte :=
  let y := expandMask p ρ'' κ
  let w := (matrixVectorNTT Â (y.map fun yi => ntt (toRq yi))).map nttInv
  let w₁ := w.map fun wi => wi.map fun c => (highBits p.γ₂ c).toNat
  (y, w, H (μ ++ w1Encode p w₁) p.ctildeLen)

/-- Lines 11–30 of Algorithm 7: the iteration of the signing loop with
counter `κ`, from `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ` and `ρ″`: the commitment hash `c̃`
and, if the validity checks pass, `(z, h)`; `none` if `SampleInBall` does
not finish within `b.ball` bytes. -/
def signIteration (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (κ : Nat) :
    Option (List Byte × Option (List Poly × List (Vector Bool n))) := do
  let (y, w, ctilde) := signCommit p Â μ ρ'' κ
  let c ← sampleInBall p.τ b.ball ctilde
  let ĉ := ntt (toRq c)
  let cs₁ := ŝ₁.map fun s => nttInv (multiplyNTT ĉ s)
  let cs₂ := ŝ₂.map fun s => nttInv (multiplyNTT ĉ s)
  let z := addVec (y.map toRq) cs₁
  let r₀ := (subVec w cs₂).map fun ri => ri.map (lowBits p.γ₂)
  if normRq z ≥ p.γ₁ - p.β ∨ normR r₀ ≥ p.γ₂ - p.β then return (ctilde, none)
  let ct₀ := t₀Hat.map fun t => nttInv (multiplyNTT ĉ t)
  let h := List.zipWith (fun u v => Vector.zipWith (makeHint p.γ₂) u v)
    (ct₀.map neg) (addVec (subVec w cs₂) ct₀)
  let ones := (h.map fun hi => (hi.toList.filter id).length).sum
  if normRq ct₀ ≥ p.γ₂ ∨ ones > p.ω then return (ctilde, none)
  return (ctilde, some (z, h))

/-- Lines 10–32 of Algorithm 7, the rejection sampling loop, from the counter
`κ`, for at most `iters` more iterations (Appendix C): the `c̃`, `z` and `h`
of the first iteration whose validity checks pass; `none` if there is none
within them, or a `SampleInBall` does not finish within `b.ball` bytes. -/
def signLoop (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : (iters κ : Nat) → Option (List Byte × List Poly × List (Vector Bool n))
  | 0, _ => none
  | iters + 1, κ => do
    match ← signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
    | (ctilde, some (z, h)) => return (ctilde, z, h)
    | (_, none) => signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)

/-- Algorithm 7, `ML-DSA.Sign_internal(sk, M′, rnd)`, with the message
representative `μ` given (line 6 "may optionally be computed in a different
cryptographic module"): the signature `σ`; `none` if a loop does not finish
within its bound. -/
def signMu (p : Params) (b : Bounds) (sk μ rnd : List Byte) : Option (List Byte) := do
  let (ρ, K, _tr, s₁, s₂, t₀) := skDecode p sk
  let ŝ₁ := s₁.map fun s => ntt (toRq s)
  let ŝ₂ := s₂.map fun s => ntt (toRq s)
  let t₀Hat := t₀.map fun t => ntt (toRq t)
  let Â ← expandA p b ρ
  let ρ'' := H (K ++ rnd ++ μ) 64
  let (ctilde, z, h) ← signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b.sign 0
  return sigEncode p ctilde (z.map fun zi => zi.map fun c => modPm c.val q) h

/-- Algorithm 7, `ML-DSA.Sign_internal(sk, M′, rnd)`: the signature `σ`;
`none` if a loop does not finish within its bound. -/
def signInternal (p : Params) (b : Bounds) (sk M' rnd : List Byte) : Option (List Byte) :=
  signMu p b sk (messageRep (skTr sk) M') rnd

/-- Algorithm 8, `ML-DSA.Verify_internal(pk, M′, σ)`, with the message
representative `μ` given (line 7 "may optionally be computed in a different
cryptographic module"): whether `σ` is a valid signature; `none` if a
`RejNTTPoly` or the `SampleInBall` does not finish within its bound. -/
def verifyMu (p : Params) (b : Bounds) (pk μ σ : List Byte) : Option Bool := do
  let (ρ, t₁) := pkDecode p pk
  let (ctilde, z, h) := sigDecode p σ
  let some h := h | return false
  let Â ← expandA p b ρ
  let c ← sampleInBall p.τ b.ball ctilde
  let ĉ := ntt (toRq c)
  let zHat := z.map fun zi => ntt (toRq zi)
  let t₁Hat := t₁.map fun ti => ntt (ti.map fun c => ofInt (c * 2 ^ d : Nat))
  let w'Approx := (subVec (matrixVectorNTT Â zHat) (scalarVectorNTT ĉ t₁Hat)).map nttInv
  let w'₁ := List.zipWith (fun hi wi => Vector.zipWith (fun hj wj => (useHint p.γ₂ hj wj).toNat) hi wi)
    h w'Approx
  let ctilde' := H (μ ++ w1Encode p w'₁) p.ctildeLen
  return decide (normR z < p.γ₁ - p.β) && ctilde == ctilde'

/-- The public key hash `tr ← H(pk, 64)` (Algorithm 6, line 9, and
Algorithm 8, line 6). -/
def pkTr (pk : List Byte) : List Byte := H pk 64

/-- Algorithm 8, `ML-DSA.Verify_internal(pk, M′, σ)`: whether `σ` is a valid
signature of `M′`; `none` if a `RejNTTPoly` or the `SampleInBall` does not
finish within its bound. -/
def verifyInternal (p : Params) (b : Bounds) (pk M' σ : List Byte) : Option Bool :=
  verifyMu p b pk (messageRep (pkTr pk) M') σ

/-! ## The external functions (§5.2, §5.3)

`ML-DSA.KeyGen`, `ML-DSA.Sign` and `ML-DSA.Verify` (Algorithms 1–3) are the
internal functions on randomness from an approved RBG, and on the message
formatted with its context string. -/

/-- `M′ ← BytesToBits(IntegerToBytes(0, 1) ‖ IntegerToBytes(|ctx|, 1) ‖ ctx) ‖ M`
(Algorithm 2, line 10, and Algorithm 3, line 5), or `⊥` (`none`) if the
context string `ctx` is longer than 255 bytes (lines 1–3). -/
def formatMessage (ctx M : List Byte) : Option (List Byte) :=
  if ctx.length > 255 then none
  else some (integerToBytes 0 1 ++ integerToBytes ctx.length 1 ++ ctx ++ M)

end VG.Spec.MlDsa

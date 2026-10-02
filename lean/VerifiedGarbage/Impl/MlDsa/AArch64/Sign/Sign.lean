import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Frag
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign`

`sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `x28`, `sk` in `x25`, `mu` in `x26`, `rnd` in `x27` and
`sig` in `x23`, and saves its caller's values of them (and of `x24` and
`x30`) in `scratch`.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `w24` the
   AND of the results. If one failed (`w24 = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`,
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `w24`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `w24 = 0`), when the checks pass (`w24 = 1`), or after 814
   iterations.
4. If `w24 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.AArch64.Sign

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params bitlen q)

/-! ## The constants of a parameter set -/

section
variable (p : Params)

/-- `λ/4`, the length of `c̃`. -/
abbrev cLen : Nat := p.ctildeLen
/-- The bound `(q - 1)/(2γ₂) - 1` of the coefficients of `w₁`. -/
abbrev w1Max : Nat := (q - 1) / (2 * p.γ₂) - 1
/-- The length of the encoding of a polynomial of `w₁`. -/
abbrev w1Len : Nat := 32 * bitlen (w1Max p)
/-- The length of the encoding of a polynomial of `z`. -/
abbrev zLen : Nat := 32 * (1 + bitlen (p.γ₁ - 1))
/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
abbrev sLen : Nat := 32 * bitlen (2 * p.η)

/-- The offsets of `s₁[r]`, `s₂[i]` and `t₀[i]` in `sk`. -/
abbrev skS1 (r : Nat) : Nat := 128 + sLen p * r
abbrev skS2 (i : Nat) : Nat := 128 + sLen p * p.ℓ + sLen p * i
abbrev skT0 (i : Nat) : Nat := 128 + sLen p * (p.ℓ + p.k) + 416 * i

/-- The offsets of `z[r]` and of the hint in `sig`. -/
abbrev sigZ (r : Nat) : Nat := cLen p + zLen p * r
abbrev sigH : Nat := cLen p + zLen p * p.ℓ

/-! ## The polynomials of the working space

`ĉ` (0), four temporaries (1–4), then `h` (`k`), `y` (`ℓ`), `ŷ` (`ℓ`),
`w` (`k`), `ŝ₁` (`ℓ`), `ŝ₂` (`k`), `t̂₀` (`k`) and `Â` (`kℓ`, row by row). -/

abbrev pS (i : Nat) : Ptr := sc (oP i)
abbrev cP : Ptr := pS 0
abbrev t1P : Ptr := pS 1
abbrev t2P : Ptr := pS 2
abbrev t3P : Ptr := pS 3
abbrev t4P : Ptr := pS 4
abbrev hP (i : Nat) : Ptr := pS (5 + i)
abbrev yP (r : Nat) : Ptr := pS (5 + p.k + r)
abbrev yhP (r : Nat) : Ptr := pS (5 + p.k + p.ℓ + r)
abbrev wP (i : Nat) : Ptr := pS (5 + p.k + 2 * p.ℓ + i)
abbrev s1P (r : Nat) : Ptr := pS (5 + 2 * p.k + 2 * p.ℓ + r)
abbrev s2P (i : Nat) : Ptr := pS (5 + 2 * p.k + 3 * p.ℓ + i)
abbrev t0P (i : Nat) : Ptr := pS (5 + 3 * p.k + 3 * p.ℓ + i)
abbrev aP (i j : Nat) : Ptr := pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j)

end

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- `ρ` to `RS`, and the `kℓ` entries of `Â`. -/
def expandA : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oRS)) (seqR (sampleE P p) 0 (p.k * p.ℓ))

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS1 p r) (sLen p) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS2 p i) (sLen p) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skT0 p i) 416 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`. -/
def decodeWith : Prog isa :=
  .seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (.seq (seqR (decT0 P p) 0 p.k)
    ((shakeAtWith c) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩)))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`, through `x9`. -/
def setKappa (r : Nat) : List Instr :=
  [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 r, .strb .x9 .x28 (oMS + 64), .lsr .x .x9 .x9 8,
    .strb .x9 .x28 (oMS + 65)]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r)) (.seq (copy (yhP p r) (yP p r) 1024) (nttAt P (yhP p r))))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def rowW (i : Nat) : Prog isa :=
  .seq (mulAt P (wP p i) (aP p i 0) (yhP p 0))
    (.seq (seqR (fun j => mulAddAt P (wP p i) (aP p i j) (yhP p j)) 1 (p.ℓ - 1)) (invNttAt P (wP p i)))

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  .seq (highBitsAt P (wP p i) p.γ₂ t1P) (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p))

/-- `y`, `ŷ`, `w`, `w₁` and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` to `CT`. -/
def commitWith : Prog isa :=
  .seq (seqR (maskR P p) 0 p.ℓ) (.seq (seqR (rowW P p) 0 p.k) (.seq (seqR (w1R P p) 0 p.k)
    ((shakeAtWith c) [⟨.x26, 0, 64⟩, ⟨.x28, oW1, p.k * w1Len p⟩] ⟨.x28, oCT, cLen p⟩)))

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` (in `y[r]`), and its norm. -/
def zR (r : Nat) : Prog isa :=
  .seq (mulAt P t1P cP (s1P p r)) (.seq (invNttAt P t1P) (.seq (addAt P (yP p r) t1P)
    (normAt P (yP p r) (p.γ₁ - p.β))))

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])` (in `w[i]`), and the norm of its `LowBits`. -/
def r0R (i : Nat) : Prog isa :=
  .seq (mulAt P t1P cP (s2P p i)) (.seq (invNttAt P t1P) (.seq (subAt P (wP p i) t1P)
    (.seq (lowBitsAt P (wP p i) p.γ₂ t2P) (normAt P t2P (p.γ₂ - p.β)))))

/-- `ct₀[i] = NTT⁻¹(ĉ t̂₀[i])` and its norm, `w[i] - cs₂[i] + ct₀[i]` (in `w[i]`),
`-ct₀[i]` (in `T4`), and `h[i] = MakeHint(-ct₀[i], w[i] - cs₂[i] + ct₀[i])`. -/
def hR (i : Nat) : Prog isa :=
  .seq (mulAt P t3P cP (t0P p i)) (.seq (invNttAt P t3P) (.seq (normAt P t3P p.γ₂)
    (.seq (copy t4P (wP p i) 1024) (.seq (addAt P (wP p i) t3P) (.seq (subAt P t4P (wP p i))
      (makeHintAt P t4P (wP p i) p.γ₂ (hP i)))))))

/-- `x24 ← x24 ∧ (ONES ≤ ω)`: `ONES - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.ldr .x .x9 .x28 oONES, .subImm .x .x9 .x9 (p.ω + 1), .lsr .x .x9 .x9 63, .logic .and .w .x24 .x24 .x9]

/-- `KAP ← KAP + ℓ`, through `x9`. -/
def kapAdd : List Instr := [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 p.ℓ, .str .x .x9 .x28 oKAP]

/-- The validity checks of an iteration, combined into `x24`; then, if they
passed, `CNT ← 1` (the loop ends with `w24 = 1`), and otherwise `κ ← κ + ℓ`. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block ([.movz .x .x24 1 0] ++ setQ (sc oONES) 0))
    (.seq (seqR (zR P p) 0 p.ℓ) (.seq (seqR (r0R P p) 0 p.k) (.seq (seqR (hR P p) 0 p.k)
      (.seq (.block (onesOk p)) (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))))))))

/-- `CNT ← CNT - 1`, left in `x9`, which the loop tests. -/
def cntDec : List Instr := [.ldr .x .x9 .x28 oCNT, .subImm .x .x9 .x9 1, .str .x .x9 .x28 oCNT]

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (and otherwise `x24 ← 0`, `CNT ← 1`); then `CNT ← CNT - 1`. -/
def iterWith : Prog isa :=
  .seq ((commitWith c) P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.ite (.nonzero .w .x0) (checks P p) (.block ([.movz .x .x24 0 0] ++ setQ (sc oCNT) 1)))
      (.block cntDec)))

/-- The rejection sampling loop: `κ ← 0`, `CNT ← 814`, and iterations while
`CNT ≠ 0`. -/
def signLoopWith : Prog isa :=
  .seq (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) (.loop ((iterWith c) P p) (.nonzero .x .x9))

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.x23, sigZ p r) (zLen p)

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (copy (.x23, 0) (sc oCT) (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.x23, sigH p) (p.ω + p.k)))

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def restWith : Prog isa := .seq ((decodeWith c) P p) (.seq ((signLoopWith c) P p) (ifOk (output P p)))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def signWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk ((restWith c) P p)) (.block epi)))

def decode := decodeWith .scalar
def commit := commitWith .scalar
def iter := iterWith .scalar
def signLoop := signLoopWith .scalar
def rest := restWith .scalar
def sign := signWith .scalar

end VG.Impl.MlDsa.AArch64.Sign

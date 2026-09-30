import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Frag

/-!
# ML-DSA on x86-64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`verify(pk = rdi, mu = rsi, sig = rdx, scratch = rcx) -> eax`:
`ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with the message
representative `μ` given (`verifyMu`), for the parameter set `p`, as calls of
the primitives `P` and of the sponge functions (`Frag.lean`). It keeps
`scratch` in `rbx`, `pk` in `rbp`, `mu` in `r12` and `sig` in `r13`, and its
result so far in `r15`; it saves its caller's values of them (and of `r14`)
in `scratch`.

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ` to polynomials
   `0, …, k - 1` (`vg_mldsa_hint_bit_unpack`); `r15` is its result, and it
   returns 0 at once if the hint is malformed.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ` (polynomial `8 + i`), and
   `r15 ← r15 ∧ (‖z[i]‖∞ < γ₁ - β)`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to `SB`, and `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   (polynomial `20 + 8r + s`); `c = SampleInBall(c̃)` (polynomial 15). Each
   sampler's result is ANDed into `r15`, and its output masked with it
   (`sampled`): a sampler that fails leaves its output unspecified, and
   masking makes it reduced (zero) without a branch on the result, which
   is not a function of the inputs when it fails.
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))` (polynomial 18),
   `w′₁ = UseHint(h[r], w′)` (polynomial 19), and its `SimpleBitPack` to
   `B + r · 32 bitlen b`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `CT`, and `r15 ← 0` unless `c̃′ = c̃`,
   without a branch.

It returns `r15`. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak) and not on
the results of the samplers.
-/

namespace VG.Impl.MlDsa.X86_64.Verify

open VG.X86_64
open VG.Spec.MlDsa

section
variable (p : Params)

/-- The length of a packed `z[i]`, `32(1 + bitlen (γ₁ - 1))` bytes. -/
def lenZ : Nat := 32 * (1 + bitlen (p.γ₁ - 1))

/-- The offset of the hint in the signature. -/
def oHint : Nat := p.ctildeLen + lenZ p * p.ℓ

/-- The bound `(q - 1)/(2γ₂) - 1` of the coefficients of `w₁`. -/
def w1Max : Nat := (q - 1) / (2 * p.γ₂) - 1

/-- The length of a packed `w₁[i]`, `32 · bitlen b`. -/
def w1Len : Nat := 32 * bitlen (w1Max p)

end

section
variable (P : Prims) (p : Params)

/-- `h` to polynomials `0, …, k - 1`, and `r15 ←` the result. -/
def hint : Prog isa :=
  .seq (hintUnpackAt P (.r13, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) (.block [.mov32 .r15 (.reg .rax)])

/-- `z[i]`, and `r15 ← r15 ∧ (‖z[i]‖∞ < γ₁ - β)`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.r13, p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ i))
    (.seq (normLtAt P (pZ i) (p.γ₁ - p.β)) (.block and15))

/-- `Â[r, s]`, entry `e = 8r + s`. -/
def aOne (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) (e % 8) ++ setB (sc (oSB + 33)) (e / 8)))
    (sampled (rejNttAt P (pS (20 + e))) (pS (20 + e)))

/-- The entries `8r + s` of row `r` of `Â`. -/
def aRow (r : Nat) : Prog isa := seqR (aOne P) (8 * r) p.ℓ

/-- `ρ` to `SB`, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (copy (sc oSB) (.rbp, 0) 32) (.seq (seqR (aRow P p) 0 p.k)
    (sampled (ballAt P (.r13, 0) p.ctildeLen p.τ pC) pC))

/-- `Σₛ Â[r, s] ẑ[s]` to `W`. -/
def dot (r : Nat) : Prog isa :=
  .seq (mulAt P pW (pA r 0) (pZ 0)) (seqR (fun s => mulAddAt P pW (pA r s) (pZ s)) 1 (p.ℓ - 1))

/-- Row `r` of `w′`, `w′₁`, packed to `B`. -/
def row (r : Nat) : Prog isa :=
  .seq (dot P p r) (.seq (unpackT1At P (.rbp, 32 + 320 * r) pT) (.seq (nttAt P pT)
    (.seq (mulAt P pT2 pT pC) (.seq (subAt P pW pT2) (.seq (invNttAt P pW)
      (.seq (useHintAt P (pH r) pW p.γ₂ pW1) (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p))))))))

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def compute : Prog isa :=
  .seq (seqR (fun i => nttAt P (pZ i)) 0 p.ℓ) (.seq (nttAt P pC) (.seq (seqR (row P p) 0 p.k)
    (.seq (hash2 (.r12, 0) 64 (sc oB) (p.k * w1Len p) (sc oCT) p.ctildeLen)
      (cmpAnd (sc oCT) (.r13, 0) p.ctildeLen))))

def body : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) (compute P p)))))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verify : Prog isa := .seq (.block pro) (.seq (body P p) (.block epi))

end

end VG.Impl.MlDsa.X86_64.Verify

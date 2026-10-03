import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen

/-!
# ML-DSA on AArch64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`verify P p (pk = x0, mu = x1, sig = x2, scratch = x3) -> w0`:
`ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with the message
representative `μ` given (`verifyMu`), for the parameter set `p`, as calls of
the primitives `P` and of the SHA-3 sponge functions (`KeyGen/Frag.lean`).
It keeps `pk` in `x25`, `mu` in `x26`, `sig` in `x27` and `scratch` in
`x28`, and its result so far in `x24`.

The layout of `scratch` (in bytes) is that of key generation where they
share a buffer: the Keccak state at 0 and the sponge functions' working
space at 200, the saved registers at 840; the recomputed commitment hash
`c̃′` at 1024 (`oCT`, at most 64 bytes); the seed of `RejNTTPoly` at 1152
(`oSA`, 34 bytes); the working space of the primitives at 2048 (2048
bytes); and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]` is
polynomial `rℓ + s`, and after them come `w1Encode(w′₁)` (at most 1024
bytes), the hint `h` (`k` polynomials), `z` (`ℓ`), `c`, two temporaries, `w′`
and `w′₁`.

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ`
   (`vg_mldsa_hint_bit_unpack`); `x24` is its result, and it returns 0 at
   once if the hint is malformed.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ`, and
   `x24 ← x24 ∧ (‖z[i]‖∞ < γ₁ - β)`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to the seed, `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   (key generation's `expA`), and `c = SampleInBall(c̃)`. Each sampler's
   result is ANDed into `x24`, and its output masked with it (`sampled`):
   a sampler that fails leaves its output unspecified, and masking makes it
   reduced (zero) without a branch on the result, which is not a function
   of the inputs when it fails.
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))`, `w′₁ = UseHint(h[r], w′)`,
   and its `SimpleBitPack` to `w1Encode(w′₁)`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)`, and `x24 ← 0` unless `c̃′ = c̃`, without
   a branch.

It returns `x24`. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak), and not on
the results of the samplers.
-/

namespace VG.Impl.MlDsa.AArch64.Verify

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Spec.MlDsa (Params bitlen q)

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

/-! ## The layout of the working space -/

/-- `c̃′`. -/
def oCT : Nat := 1024

/-- The polynomial `j` after `Â`. -/
abbrev vP (j : Nat) : Ptr := sc (oP (p.k * p.ℓ + j))

/-- `w1Encode(w′₁)` (at most 1024 bytes), first, so that its offset is below 2¹⁶, which the sponge takes. -/
abbrev bP : Ptr := vP p 0
abbrev hP (r : Nat) : Ptr := vP p (1 + r)
abbrev zP (i : Nat) : Ptr := vP p (1 + p.k + i)
abbrev cP : Ptr := vP p (1 + p.k + p.ℓ)
abbrev tmP : Ptr := vP p (1 + p.k + p.ℓ + 1)
abbrev tm2P : Ptr := vP p (1 + p.k + p.ℓ + 2)
abbrev wP : Ptr := vP p (1 + p.k + p.ℓ + 3)
abbrev w1P : Ptr := vP p (1 + p.k + p.ℓ + 4)

end

/-! ## The comparison -/

/-- One byte of `a ⊕ b` ORed into `x10`. -/
def cmpBody : List Instr :=
  [.ldrb .x9 .x0 0, .ldrb .x11 .x1 0, .logic .eor .x .x9 .x9 .x11, .logic .orr .x .x10 .x10 .x9,
    .addImm .x .x0 .x0 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]

/-- `x24 ← 0` unless the `n` bytes at `a` and `b` are equal, without a
branch: `x10` is the OR of the XORs of their bytes, so 0 exactly when they
are equal, and `(x10 - 1) >> 63` then 1, and 0 otherwise. -/
def cmpAnd (a b : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (glue [(.x0, .ptr a), (.x1, .ptr b), (.x2, .imm n)] ++ ([.movz .x .x10 0 0] : List Instr)))
    (.seq (.loop (.block cmpBody) (.nonzero .x .x2))
      (.block [.subImm .x .x10 .x10 1, .lsr .x .x10 .x10 63, .logic .and .w .x24 .x24 .x10]))

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `h`, and `x24 ←` the result. -/
def hint : Prog isa :=
  .seq (hintUnpackAt P (.x27, oHint p) (p.ω + p.k) p.ω (hP p 0) (256 * p.k)) (.block and24)

/-- `z[i]`, and `x24 ← x24 ∧ (‖z[i]‖∞ < γ₁ - β)`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x27, p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ (zP p i))
    (.seq (normLtAt P (zP p i) (p.γ₁ - p.β)) (.block and24))

/-- `ρ` to the seed, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (.block (copy32 .x25 0 .x28 oSA)) (.seq (expAll P p)
    (sampled (ballAt P (sc oSS) (.x27, 0) p.ctildeLen p.τ (cP p)) (cP p)))

/-- `Σₛ Â[r, s] ẑ[s]` to `w′`. -/
def dot (r : Nat) : Prog isa :=
  .seq (mulAt P (wP p) (aP (p.ℓ * r)) (zP p 0))
    (seqR (fun s => mulAddAt P (wP p) (aP (p.ℓ * r + s)) (zP p s)) 1 (p.ℓ - 1))

/-- Row `r` of `w′`, `w′₁`, packed to `w1Encode(w′₁)`. -/
def row (r : Nat) : Prog isa :=
  .seq (dot P p r) (.seq (unpackT1At P (.x25, 32 + 320 * r) (tmP p)) (.seq (nttAt P (sc oSS) (tmP p))
    (.seq (mulAt P (tm2P p) (cP p) (tmP p)) (.seq (subAt P (wP p) (tm2P p)) (.seq (invNttAt P (sc oSS) (wP p))
      (.seq (useHintAt P (hP p r) (wP p) p.γ₂ (w1P p))
        (simpleBitPackAt P (w1P p) (w1Max p) ((bP p).1, (bP p).2 + w1Len p * r) (w1Len p))))))))

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def computeWith : Prog isa :=
  .seq (seqR (fun i => nttAt P (sc oSS) (zP p i)) 0 p.ℓ) (.seq (nttAt P (sc oSS) (cP p))
    (.seq (seqR (row P p) 0 p.k)
    (.seq ((shake256With c) [⟨.x26, 0, 64⟩, ⟨.x28, (bP p).2, p.k * w1Len p⟩] [⟨.x28, oCT, p.ctildeLen⟩])
      (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen))))

def bodyWith : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) ((computeWith c) P p)))))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verifyWith : Prog isa := .seq (.block pro) (.seq ((bodyWith c) P p) (.block epi))

end

def compute := computeWith .scalar
def body := bodyWith .scalar
def verify := verifyWith .scalar

end VG.Impl.MlDsa.AArch64.Verify

import VerifiedGarbage.Impl.MlDsa.X86.Sign.Frag
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa{44,65,87}_sign`

`sign(sk, mu, rnd, sig, scratch) -> eax`: `ML-DSA.Sign_internal(sk, M′, rnd)`
(FIPS 204 Algorithm 7) with the message representative `μ` given
(`Spec.MlDsa.signMu`), for the parameter set `p`, as calls of the
primitives `P` and the sponge functions (`Frag.lean`). It saves its
caller's registers in a frame of 16 bytes (`leaf`), keeps `scratch` in
`esi`, and reads the other arguments from the stack.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `OK` the
   AND of the results. If one failed (`OK = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, with `K ‖ rnd` copied to
   `HIN` first.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`,
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `OK`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `OK = 0`), when the checks pass (`OK = 1`), or after 814
   iterations.
4. If `OK = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

It returns `OK`. Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are
`ρ` and two indices), and the branch on their results, depend on `ρ`; only
the calls of `vg_mldsa_sample_in_ball`, and the branch on their results, on
`c̃`; only the branch on the validity checks on whether they passed, and
only the call of `vg_mldsa_hint_bit_pack` on the hint of the signature.
Every other address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86.Sign

open VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo callWith callRet at_ copyW leaf)
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

/-! ## The buffers of the arguments -/

abbrev bSk (off len : Nat) : Buf := ⟨0, off, len⟩
abbrev bMu : Buf := ⟨1, 0, 64⟩
abbrev bRnd : Buf := ⟨2, 0, 32⟩
abbrev bSig (off len : Nat) : Buf := ⟨3, off, len⟩

/-! ## The polynomials of the working space

`ĉ` (0), four temporaries (1–4), then `h` (`k`), `y` (`ℓ`), `ŷ` (`ℓ`),
`w` (`k`), `ŝ₁` (`ℓ`), `ŝ₂` (`k`), `t̂₀` (`k`) and `Â` (`kℓ`, row by row). -/

abbrev cP : Buf := pS 0
abbrev t1P : Buf := pS 1
abbrev t2P : Buf := pS 2
abbrev t3P : Buf := pS 3
abbrev t4P : Buf := pS 4
abbrev hP (i : Nat) : Buf := pS (5 + i)
abbrev yP (r : Nat) : Buf := pS (5 + p.k + r)
abbrev yhP (r : Nat) : Buf := pS (5 + p.k + p.ℓ + r)
abbrev wP (i : Nat) : Buf := pS (5 + p.k + 2 * p.ℓ + i)
abbrev s1P (r : Nat) : Buf := pS (5 + 2 * p.k + 2 * p.ℓ + r)
abbrev s2P (i : Nat) : Buf := pS (5 + 2 * p.k + 3 * p.ℓ + i)
abbrev t0P (i : Nat) : Buf := pS (5 + 3 * p.k + 3 * p.ℓ + i)
abbrev aP (i j : Nat) : Buf := pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j)

end

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (st8 (oRS + 32) (e % p.ℓ) ++ st8 (oRS + 33) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- `ρ` to `RS`, and the `kℓ` entries of `Â`. -/
def expandA : Prog isa := .seq (copyW SC (bSk 0 32) (sc oRS 32) 8) (seqR (sampleE P p) 0 (p.k * p.ℓ))

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (bSk (skS1 p r) (sLen p)) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (bSk (skS2 p i) (sLen p)) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (bSk (skT0 p i) 416) 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`. -/
def decode : Prog isa :=
  .seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (.seq (seqR (decT0 P p) 0 p.k)
    (.seq (copyW SC (bSk 32 32) (sc oHIN 32) 8) (.seq (copyW SC bRnd (sc (oHIN + 32) 32) 8)
      (shake2 (sc oHIN 64) bMu (sc oMS 64))))))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`. -/
def setKappa (r : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi oKAP)), .alu .add .eax (.imm (BitVec.ofNat 32 r)), .store8 (at_ .esi (oMS + 64)) .al,
    .shift .shr .eax 8, .store8 (at_ .esi (oMS + 65)) .al]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r))
    (.seq (copyW SC (yP p r) (yhP p r) 256) (nttAt P (yhP p r))))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def rowW (i : Nat) : Prog isa :=
  .seq (mulAt P (wP p i) (aP p i 0) (yhP p 0))
    (.seq (seqR (fun j => mulAddAt P (wP p i) (aP p i j) (yhP p j)) 1 (p.ℓ - 1)) (invNttAt P (wP p i)))

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  .seq (highBitsAt P (wP p i) p.γ₂ t1P) (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i) (w1Len p)))

/-- `y`, `ŷ`, `w`, `w₁` and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` to `CT`. -/
def commit : Prog isa :=
  .seq (seqR (maskR P p) 0 p.ℓ) (.seq (seqR (rowW P p) 0 p.k) (.seq (seqR (w1R P p) 0 p.k)
    (shake2 bMu (sc oW1 (p.k * w1Len p)) (sc oCT (cLen p)))))

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
    (.seq (copyW SC (wP p i) t4P 256) (.seq (addAt P (wP p i) t3P) (.seq (subAt P t4P (wP p i))
      (makeHintAt P t4P (wP p i) p.γ₂ (hP i)))))))

/-- `OK ← OK ∧ (ONES ≤ ω)`: `ONES - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.mov .eax (.mem (at_ .esi oONES)), .alu .sub .eax (.imm (BitVec.ofNat 32 (p.ω + 1))), .shift .shr .eax 31] ++
    andOK

/-- `κ ← κ + ℓ`. -/
def nextKappa : List Instr :=
  [.mov .eax (.mem (at_ .esi oKAP)), .alu .add .eax (.imm (BitVec.ofNat 32 p.ℓ)), .store (at_ .esi oKAP) .eax]

/-- The validity checks of an iteration, combined into `OK`; then, if they
passed, `CNT ← 1` (the loop ends with `OK = 1`), and otherwise `κ ← κ + ℓ`. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block (st32 oOK 1 ++ st32 oONES 0))
    (.seq (seqR (zR P p) 0 p.ℓ) (.seq (seqR (r0R P p) 0 p.k) (.seq (seqR (hR P p) 0 p.k)
      (.seq (.block (onesOk p)) (ifOkElse (.block (st32 oCNT 1)) (.block (nextKappa p))))))))

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (and otherwise `OK ← 0`, `CNT ← 1`); then `CNT ← CNT - 1`, which
sets ZF when the loop ends. -/
def iter : Prog isa :=
  .seq (commit P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.block [.alu .test .eax (.reg .eax)])
      (.seq (.ite .ne (checks P p) (.block (st32 oOK 0 ++ st32 oCNT 1)))
        (.block [.mov .eax (.mem (at_ .esi oCNT)), .alu .sub .eax (.imm 1), .store (at_ .esi oCNT) .eax]))))

/-- The rejection sampling loop: `κ ← 0`, `CNT ← 814`, and iterations while
`CNT ≠ 0`. -/
def signLoop : Prog isa :=
  .seq (.block (st32 oKAP 0 ++ st32 oCNT 814)) (.loop (iter P p) .ne)

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (bSig (sigZ p r) (zLen p))

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (copyW SC (sc oCT (cLen p)) (bSig 0 (cLen p)) (cLen p / 4)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (sc (oP 5) (1024 * p.k)) p.ω (bSig (sigH p) (p.ω + p.k))))

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def rest : Prog isa := .seq (decode P p) (.seq (signLoop P p) (ifOk (output P p)))

/-- The body: `esi ← scratch`, `OK ← 1`, `Â`, and the rest if every entry
of `Â` was sampled; then `eax ← OK`. -/
def body : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * SC)))]) (.seq (.block (st32 oOK 1))
    (.seq (expandA P p) (.seq (ifOk (rest P p)) (.block [.mov .eax (.mem (at_ .esi oOK))]))))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def sign (P : Prims) (p : Params) : Prog isa := leaf (body P p)

end VG.Impl.MlDsa.X86.Sign

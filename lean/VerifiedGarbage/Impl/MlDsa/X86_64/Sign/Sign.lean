import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Frag
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86-64: `vg_mldsa{44,65,87}_sign`

`sign(sk = rdi, mu = rsi, rnd = rdx, sig = rcx, scratch = r8) -> eax`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `rbx`, `sk` in `rbp`, `mu` in `r12`, `rnd` in `r13` and
`sig` in `r14`, and saves its caller's values of them (and of `r15`) in
`scratch`.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   to each of the four seeds at `RS4`, and `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   for the `kℓ` entries: four consecutive entries at a time
   (`vg_mldsa_rej_ntt_poly4`, each seed at `RS4` with its entry's indices),
   then the last `kℓ mod 4` one at a time, with `r15` the AND of the
   results. If one failed (`r15 = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`:
   four polynomials at a time (`vg_mldsa_expand_mask_poly4`, from the seeds
   `ρ″ ‖ κ + r` at `MS4`), then the last `ℓ mod 4` one at a time;
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `r15`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `r15 = 0`), when the checks pass (`r15 = 1`), or after 814
   iterations.
4. If `r15 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` and `vg_mldsa_rej_ntt_poly4`
(whose seeds are `ρ` and two indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Sign

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)
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
`w` (`k`), `ŝ₁` (`ℓ`), `ŝ₂` (`k`), `t̂₀` (`k`) and `Â` (`kℓ`, row by row), then the
working space of `vg_mldsa_rej_ntt_poly4` (8 KiB). -/

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
/-- Entry `e = ℓi + j` of `Â`. -/
abbrev aE (e : Nat) : Ptr := pS (5 + 4 * p.k + 3 * p.ℓ + e)
/-- The working space of `vg_mldsa_rej_ntt_poly4`. -/
abbrev r4P : Ptr := pS (5 + 4 * p.k + 3 * p.ℓ + p.k * p.ℓ)

end

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- `ρ` to seed `k` of `RS4`. -/
def cpR4 (k : Nat) : Prog isa := copy (sc (oRS4 + 34 * k)) (.rbp, 0) 32

/-- The indices of entry `e + k` of `Â` to seed `k` of `RS4`. -/
def setSR (e k : Nat) : List Instr :=
  setB (sc (oRS4 + 34 * k + 32)) ((e + k) % p.ℓ) ++ setB (sc (oRS4 + 34 * k + 33)) ((e + k) / p.ℓ)

/-- Entries `4g, …, 4g + 3` of `Â`. -/
def sample4 (g : Nat) : Prog isa :=
  .seq (.block (setSR p (4 * g) 0)) (.seq (.block (setSR p (4 * g) 1)) (.seq (.block (setSR p (4 * g) 2))
    (.seq (.block (setSR p (4 * g) 3)) (rej4At P (aE p (4 * g)) (r4P p)))))

/-- `ρ` to `RS` and to the four seeds of `RS4`, and the `kℓ` entries of `Â`: four at a time, then
the last `kℓ mod 4` one at a time. -/
def expandA : Prog isa :=
  .seq (copy (sc oRS) (.rbp, 0) 32) (.seq (seqR cpR4 0 4)
    (.seq (seqR (sample4 P p) 0 (p.k * p.ℓ / 4)) (seqR (sampleE P p) (4 * (p.k * p.ℓ / 4)) (p.k * p.ℓ % 4))))

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.rbp, skS1 p r) (sLen p) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.rbp, skS2 p i) (sLen p) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.rbp, skT0 p i) 416 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`. -/
def decode : Prog isa :=
  .seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (.seq (seqR (decT0 P p) 0 p.k)
    (shakeAt [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64)))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `scratch + o`. -/
def setKap (o r : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbx oKAP)), .alu .add .rax (.imm (BitVec.ofNat 32 r)), .store8 (at_ .rbx o) .rax,
    .shift .shr .rax 8, .store8 (at_ .rbx (o + 1)) .rax]

/-- The two bytes of `κ + r` to `MS + 64`. -/
def setKappa (r : Nat) : List Instr := setKap (oMS + 64) r

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r)) (.seq (copy (yhP p r) (yP p r) 1024) (nttAt P (yhP p r))))

/-- `ŷ[r] = NTT(y[r])`. -/
def yhR (r : Nat) : Prog isa := .seq (copy (yhP p r) (yP p r) 1024) (nttAt P (yhP p r))

/-- `ρ″ ‖ κ + 4g + k` to seed `k` of `MS4`. -/
def cpM4 (g k : Nat) : Prog isa :=
  .seq (copy (sc (oMS4 + 66 * k)) (sc oMS) 64) (.block (setKap (oMS4 + 66 * k + 64) (4 * g + k)))

/-- `y[4g], …, y[4g + 3]`, four at a time, and their `ŷ`. -/
def mask4 (g : Nat) : Prog isa :=
  .seq (seqR (cpM4 g) 0 4) (.seq (mask4At P p.γ₁ (yP p (4 * g)) (r4P p)) (seqR (yhR P p) (4 * g) 4))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def rowW (i : Nat) : Prog isa :=
  .seq (mulAt P (wP p i) (aP p i 0) (yhP p 0))
    (.seq (seqR (fun j => mulAddAt P (wP p i) (aP p i j) (yhP p j)) 1 (p.ℓ - 1)) (invNttAt P (wP p i)))

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  .seq (highBitsAt P (wP p i) p.γ₂ t1P) (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p))

/-- `y`, `ŷ`, `w`, `w₁` and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` to `CT`. -/
def commit : Prog isa :=
  .seq (seqR (mask4 P p) 0 (p.ℓ / 4)) (.seq (seqR (maskR P p) (4 * (p.ℓ / 4)) (p.ℓ % 4))
    (.seq (seqR (rowW P p) 0 p.k) (.seq (seqR (w1R P p) 0 p.k)
      (shakeAt [((.r12, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p)))))

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

/-- `r15 ← r15 ∧ (ONES ≤ ω)`: `ONES - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.mov32 .rax (.mem (at_ .rbx oONES)), .alu .sub .rax (.imm (BitVec.ofNat 32 (p.ω + 1))), .shift .shr .rax 63,
    .alu32 .and .r15 (.reg .rax)]

/-- The validity checks of an iteration, combined into `r15`; then, if they
passed, `CNT ← 1` (the loop ends with `r15 = 1`), and otherwise `κ ← κ + ℓ`. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block ([.mov32 .r15 (.imm 1)] ++ setQ (sc oONES) 0))
    (.seq (seqR (zR P p) 0 p.ℓ) (.seq (seqR (r0R P p) 0 p.k) (.seq (seqR (hR P p) 0 p.k)
      (.seq (.block (onesOk p)) (ifOkElse (.block (setQ (sc oCNT) 1))
        (.block [.mov .rax (.mem (at_ .rbx oKAP)), .alu .add .rax (.imm (BitVec.ofNat 32 p.ℓ)),
          .store (at_ .rbx oKAP) .rax])))))))

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (and otherwise `r15 ← 0`, `CNT ← 1`); then `CNT ← CNT - 1`, which
sets ZF when the loop ends. -/
def iter : Prog isa :=
  .seq (commit P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.block [.alu32 .test .rax (.reg .rax)]) (.seq (.ite .ne (checks P p) (.block ([.mov32 .r15 (.imm 0)] ++ setQ (sc oCNT) 1)))
      (.block [.mov .rax (.mem (at_ .rbx oCNT)), .alu .sub .rax (.imm 1), .store (at_ .rbx oCNT) .rax]))))

/-- The rejection sampling loop: `κ ← 0`, `CNT ← 814`, and iterations while
`CNT ≠ 0`. -/
def signLoop : Prog isa :=
  .seq (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) (.loop (iter P p) .ne)

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa := bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.r14, sigZ p r) (zLen p)

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (copy (.r14, 0) (sc oCT) (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.r14, sigH p) (p.ω + p.k)))

def pro : List Instr := topPro .r8 [(.rbp, .rdi), (.r12, .rsi), (.r13, .rdx), (.r14, .rcx)]

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def rest : Prog isa := .seq (decode P p) (.seq (signLoop P p) (ifOk (output P p)))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def sign (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk (rest P p)) (.block topEpi)))

end VG.Impl.MlDsa.X86_64.Sign

import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Frag

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`verify P p (pk = r0, mu = r1, sig = r2, scratch = r3) -> r0`:
`ML-DSA.Verify_internal(pk, M′, σ)` (FIPS 204 Algorithm 8) with the message
representative `μ` given (`verifyMu`), for the parameter set `p`, as calls of
the primitives `P` and of the sponge functions (`KeyGen/Frag.lean`). It keeps
`pk` in `r4`, `mu` in `r5`, `sig` in `r6`, `scratch` in `r7`, and its result
so far in `r11`; it saves our caller's `r4`–`r11` and `lr` in `scratch`.

The layout of `scratch` (in bytes): the Keccak state at 0 (200 bytes) and
the sponge functions' working space at 200 (640 bytes); our caller's
registers at 840 (36 bytes); the seed of `RejNTTPoly` (`SB`, 34 bytes) at
896; `w1Encode(w′₁)` at 1024 (at most 1024 bytes); the recomputed commitment
hash `c̃′` at 2048 (at most 64 bytes); the working space of the primitives
at 4096 (2048 bytes); and polynomials of 1024 bytes from 8192 (`oP j`): the
hint `h` (polynomials 0 to 7, of which the first `k`), `z` (8 to 14), `c`
(15), two temporaries (16, 17), `w′` (18), `w′₁` (19), and `Â[r, s]`
(`20 + 8r + s`).

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ` to polynomials
   `0, …, k - 1` (`vg_mldsa_hint_bit_unpack`); `r11` is its result, and it
   returns 0 at once if the hint is malformed.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ` (polynomial `8 + i`), and
   `r11 ← r11 ∧ (‖z[i]‖∞ < γ₁ - β)`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to `SB`, and `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`
   (polynomial `20 + 8r + s`); `c = SampleInBall(c̃)` (polynomial 15). Each
   sampler's result is ANDed into `r11`, and its output masked with it
   (`sampled`): a sampler that fails leaves its output unspecified, and
   masking makes it reduced (zero) without a branch on the result, which
   is not a function of the inputs when it fails.
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))` (polynomial 18),
   `w′₁ = UseHint(h[r], w′)` (polynomial 19), and its `SimpleBitPack` to
   `1024 + r · 32 bitlen b`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `2048`, and `r11 ← 0` unless
   `c̃′ = c̃`, without a branch.

It returns `r11`. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak) and not on
the results of the samplers.
-/

namespace VG.Impl.MlDsa.Arm.Verify

open VG.Arm
open VG.Impl.MlKem.Arm (hash copy topEnd cmpBody)
open VG.Impl.MlDsa.Arm.KeyGen (Ptr Arg callAt callAtS setB seqR and11 sampled pro ldc)
open VG.Spec.MlDsa

/-- The code of the primitives `vg_mldsa_*` that verification calls. -/
structure Prims where
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  sub : Prog isa
  rejNtt : Prog isa
  ball : Prog isa
  useHint : Prog isa
  simpleBitPack : Prog isa
  bitUnpack : Prog isa
  unpackT1 : Prog isa
  hintUnpack : Prog isa
  normLt : Prog isa

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

/-! ## The layout of the working space -/

def oSB : Nat := 896
def oB : Nat := 1024
def oCT : Nat := 2048
def oSS : Nat := 4096
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 8192 + 1024 * j

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.r7, off)

/-- Polynomial `j` of the working space. -/
abbrev pS (j : Nat) : Ptr := sc (oP j)

abbrev pH (r : Nat) : Ptr := pS r
abbrev pZ (i : Nat) : Ptr := pS (8 + i)
abbrev pC : Ptr := pS 15
abbrev pT : Ptr := pS 16
abbrev pT2 : Ptr := pS 17
abbrev pW : Ptr := pS 18
abbrev pW1 : Ptr := pS 19
abbrev pA (r s : Nat) : Ptr := pS (20 + 8 * r + s)

/-! ## The primitives -/

section
variable (P : Prims)

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.r0, .ptr f), (.r1, .ptr (sc oSS))]

def invNttAt (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_inv_ntt" P.invNtt [(.r0, .ptr f), (.r1, .ptr (sc oSS))]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.r0, .ptr h), (.r1, .ptr f), (.r2, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.r0, .ptr h), (.r1, .ptr f), (.r2, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.r0, .ptr f), (.r1, .ptr g)]

def rejNttAt (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_rej_ntt_poly" P.rejNtt [(.r0, .ptr (sc oSB)), (.r1, .ptr a), (.r2, .ptr (sc oSS))]

def ballAt (ct : Ptr) (len tau : Nat) (c : Ptr) : Prog isa :=
  callAtS "vg_mldsa_sample_in_ball" P.ball [(.r0, .ptr ct), (.r1, .imm len), (.r2, .imm tau), (.r3, .ptr c)]
    (.ptr (sc oSS))

def useHintAt (h r : Ptr) (g2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_use_hint" P.useHint [(.r0, .ptr h), (.r1, .ptr r), (.r2, .imm g2), (.r3, .ptr out)]

def sbpAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack [(.r0, .ptr f), (.r1, .imm b), (.r2, .ptr out), (.r3, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAtS "vg_mldsa_bit_unpack" P.bitUnpack [(.r0, .ptr v), (.r1, .imm len), (.r2, .imm a), (.r3, .imm b)]
    (.ptr f)

def unpackT1At (v f : Ptr) : Prog isa :=
  callAt "vg_mldsa_unpack_t1" P.unpackT1 [(.r0, .ptr v), (.r1, .ptr f)]

def hintUnpackAt (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : Prog isa :=
  callAtS "vg_mldsa_hint_bit_unpack" P.hintUnpack [(.r0, .ptr y), (.r1, .imm len), (.r2, .imm omega), (.r3, .ptr h)]
    (.imm hlen)

def normLtAt (f : Ptr) (bound : Nat) : Prog isa :=
  callAt "vg_mldsa_norm_lt" P.normLt [(.r0, .ptr f), (.r1, .imm bound)]

end

/-! ## Control -/

/-- `c` if `r11 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := .seq (.block [.cmp .r11 (.imm 0)]) (.ite .ne c (.block []))

/-- `r11 ← 0` unless the `n` bytes at `a` and `b` are equal, without a
branch: `r12` is the OR of the XORs of their bytes (`cmpBody`), so 0 exactly
when they are equal, and then `(r12 - 1) >> 31` is 1 (and 0 otherwise, as
`r12 < 256`). -/
def cmpAnd (a b : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (Arg.instrs .r0 (.ptr a) ++ Arg.instrs .r1 (.ptr b) ++ ldc .r9 n ++ [.mov .r12 (.imm 0)]))
    (.seq (.loop (.block cmpBody) .ne)
      (.block [.dp .sub .r12 .r12 (.imm 1), .mov .r12 (.shifted .r12 .lsr 31), .dp .and .r11 .r11 (.reg .r12)]))

/-! ## The function -/

section
variable (P : Prims) (p : Params)

/-- `h` to polynomials `0, …, k - 1`, and `r11 ←` the result. -/
def hint : Prog isa :=
  .seq (hintUnpackAt P (.r6, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) (.block [.mov .r11 (.reg .r0)])

/-- `z[i]`, and `r11 ← r11 ∧ (‖z[i]‖∞ < γ₁ - β)`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.r6, p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ i))
    (.seq (normLtAt P (pZ i) (p.γ₁ - p.β)) (.block and11))

/-- `Â[r, s]`, entry `e = 8r + s`. -/
def aOne (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) (e % 8) ++ setB (sc (oSB + 33)) (e / 8)))
    (sampled (rejNttAt P (pS (20 + e))) (pS (20 + e)))

/-- The entries `8r + s` of row `r` of `Â`. -/
def aRow (r : Nat) : Prog isa := seqR (aOne P) (8 * r) p.ℓ

/-- `ρ` to `SB`, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (copy .r4 0 .r7 oSB 32) (.seq (seqR (aRow P p) 0 p.k)
    (sampled (ballAt P (.r6, 0) p.ctildeLen p.τ pC) pC))

/-- `Σₛ Â[r, s] ẑ[s]` to `W`. -/
def dot (r : Nat) : Prog isa :=
  .seq (mulAt P pW (pA r 0) (pZ 0)) (seqR (fun s => mulAddAt P pW (pA r s) (pZ s)) 1 (p.ℓ - 1))

/-- Row `r` of `w′`, `w′₁`, packed to `B`. -/
def row (r : Nat) : Prog isa :=
  .seq (dot P p r) (.seq (unpackT1At P (.r4, 32 + 320 * r) pT) (.seq (nttAt P pT)
    (.seq (mulAt P pT2 pC pT) (.seq (subAt P pW pT2) (.seq (invNttAt P pW)
      (.seq (useHintAt P (pH r) pW p.γ₂ pW1) (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p))))))))

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def compute : Prog isa :=
  .seq (seqR (fun i => nttAt P (pZ i)) 0 p.ℓ) (.seq (nttAt P pC) (.seq (seqR (row P p) 0 p.k)
    (.seq (hash 136 0x1f [⟨.r5, 0, 64⟩, ⟨.r7, oB, p.k * w1Len p⟩] [⟨.r7, oCT, p.ctildeLen⟩])
      (cmpAnd (sc oCT) (.r6, 0) p.ctildeLen))))

def body : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) (compute P p)))))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verify : Prog isa := .seq (.block pro) (.seq (body P p) (.block topEnd))

end

end VG.Impl.MlDsa.Arm.Verify

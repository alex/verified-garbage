import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Call
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`verify P p (pk, mu, sig, scratch) -> eax`: `ML-DSA.Verify_internal(pk, M′, σ)`
(FIPS 204 Algorithm 8) with the message representative `μ` given
(`verifyMu`), for the parameter set `p`, as calls of the primitives `P`
(`Prims`, any implementations of them) and of the SHA-3 sponge functions. As
key generation (`Impl/MlDsa/X86/KeyGen/`), it is a leaf that keeps `scratch`
(argument 3) in `esi`, and its result so far in the word `oACC` of
`scratch`.

The layout of `scratch` (in bytes): the Keccak state at 0 and the sponge
functions' working space at 200; the result at 900 (`oACC`); the seed of
`RejNTTPoly` at 1152 (`oSB`, 34 bytes); `w1Encode(w′₁)` at 2048 (`oB`, at
most 1024 bytes); `c̃′` at 3072 (`oCT`, at most 64 bytes); the working space
of the primitives at 4096 (2048 bytes); and polynomials of 1024 bytes from
8192 (`oP j`): the hint `h` (polynomials 0 to `k - 1`), `z` (8 to 14), `c`
(15), two temporaries (16, 17), `w′` (18), `w′₁` (19), and `Â[r, s]`
(`20 + 8r + s`).

1. `h ← HintBitUnpack` of the last `ω + k` bytes of `σ`, and the result is
   its value: 0 if the hint is malformed, and then it returns 0.
2. `z[i] = BitUnpack` of the `i`-th piece of `σ`, and the result ANDed with
   `‖z[i]‖∞ < γ₁ - β`; it returns 0 if one of them is not.
3. `ρ` (`pk[0 : 32]`) to the seed, `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` and
   `c = SampleInBall(c̃)`: each sampler's result is ANDed into the result, and
   its output masked with it (`maskA`), so that it is reduced whatever the
   sampler returns, without a branch on it.
4. `ẑ[i] = NTT(z[i])`, `ĉ = NTT(c)`; for each row `r`:
   `w′ = NTT⁻¹(Σₛ Â[r, s] ẑ[s] - ĉ · NTT(t₁[r] · 2ᵈ))`, `w′₁ = UseHint(h[r], w′)`,
   and its `SimpleBitPack` to `oB + r · 32 bitlen b`.
5. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `oCT`, and the result ANDed with
   `c̃′ = c̃`, without a branch.

It returns the result. Every address and branch depends only on the pointers,
the public key and the signature (which the function may leak), and not on
the results of the samplers.
-/

namespace VG.Impl.MlDsa.X86.Verify

open VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo st8 copyW maskA hash2 leaf at_)
open VG.Impl.MlDsa.X86.KeyGen (Arg callP callPR seqR)
open VG.Spec.MlDsa (Params bitlen q)

/-- The code of the primitives verification calls. -/
structure Prims where
  /-- `vg_mldsa_ntt` -/
  ntt : Prog isa
  /-- `vg_mldsa_inv_ntt` -/
  invNtt : Prog isa
  /-- `vg_mldsa_multiply_ntt` -/
  mul : Prog isa
  /-- `vg_mldsa_multiply_add_ntt` -/
  mulAdd : Prog isa
  /-- `vg_mldsa_sub` -/
  sub : Prog isa
  /-- `vg_mldsa_rej_ntt_poly` -/
  rejNtt : Prog isa
  /-- `vg_mldsa_sample_in_ball` -/
  ball : Prog isa
  /-- `vg_mldsa_use_hint` -/
  useHint : Prog isa
  /-- `vg_mldsa_simple_bit_pack` -/
  simpleBitPack : Prog isa
  /-- `vg_mldsa_bit_unpack` -/
  bitUnpack : Prog isa
  /-- `vg_mldsa_unpack_t1` -/
  unpackT1 : Prog isa
  /-- `vg_mldsa_hint_bit_unpack` -/
  hintUnpack : Prog isa
  /-- `vg_mldsa_norm_lt` -/
  normLt : Prog isa

/-! ## The layout of the working space -/

/-- `scratch` is argument 3. -/
abbrev vS : Nat := 3
def oACC : Nat := 900
def oSB : Nat := 1152
def oB : Nat := 2048
def oCT : Nat := 3072
def oSS : Nat := 4096
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 8192 + 1024 * j

/-- A buffer of `scratch`. -/
abbrev sb (o l : Nat) : Buf := ⟨vS, o, l⟩
/-- Polynomial `j` of `scratch`. -/
abbrev pB (j : Nat) : Buf := sb (oP j) 1024
abbrev pZ (i : Nat) : Buf := pB (8 + i)
abbrev pC : Buf := pB 15
abbrev pT : Buf := pB 16
abbrev pT2 : Buf := pB 17
abbrev pW : Buf := pB 18
abbrev pW1 : Buf := pB 19
abbrev pA (r s : Nat) : Buf := pB (20 + 8 * r + s)
/-- The hint, as `k` polynomials. -/
abbrev hB (k : Nat) : Buf := sb (oP 0) (256 * k * 4)
/-- The working space of the primitives. -/
abbrev ssB (l : Nat) : Buf := sb oSS l

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

/-! ## The result -/

/-- The result ANDed with `eax`. -/
def accAnd : List Instr :=
  [.mov .ecx (.mem (at_ .esi oACC)), .alu .and .ecx (.reg .eax), .store (at_ .esi oACC) .ecx]

/-- `c` if the result is not 0. -/
def ifOk (c : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esi oACC)), .alu .test .eax (.reg .eax)]) (.ite .ne c (.block []))

/-- The OR of the XORs of the bytes at `edi` and `ebp`, to `edx`. -/
def cmpBody : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .movzx8 .ebx (at_ .ebp 0), .alu .xor .eax (.reg .ebx), .alu .or .edx (.reg .eax),
    .alu .add .edi (.imm 1), .alu .add .ebp (.imm 1), .alu .sub .ecx (.imm 1)]

/-- The result ANDed with the equality of the `n` bytes at `a` and `b`, without a
branch: `edx` is the OR of the XORs of their bytes, so 0 exactly when they
are equal (`sub edx, 1` borrows then), and `eax` the mask `-borrow`. -/
def cmpAnd (a b : Buf) (n : Nat) : Prog isa :=
  .seq (.block (ptrTo vS .edi a ++ ptrTo vS .ebp b ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 n)), .mov .edx (.imm 0)] : List Instr)))
    (.seq (.loop (.block cmpBody) .ne) (.block ([.alu .sub .edx (.imm 1), .alu .sbb .eax (.reg .eax)] ++ accAnd)))

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `h`, and the result its value. -/
def hint : Prog isa :=
  .seq (callPR vS "vg_mldsa_hint_bit_unpack" P.hintUnpack
      [.buf ⟨2, oHint p, p.ω + p.k⟩, .imm (p.ω + p.k), .imm p.ω, .buf (hB p.k), .imm (256 * p.k)])
    (.block [.store (at_ .esi oACC) .eax])

/-- `z[i]`, and the result ANDed with `‖z[i]‖∞ < γ₁ - β`. -/
def zOne (i : Nat) : Prog isa :=
  .seq (callP vS "vg_mldsa_bit_unpack" P.bitUnpack
      [.buf ⟨2, p.ctildeLen + lenZ p * i, lenZ p⟩, .imm (lenZ p), .imm (p.γ₁ - 1), .imm p.γ₁, .buf (pZ i)])
    (.seq (callPR vS "vg_mldsa_norm_lt" P.normLt [.buf (pZ i), .imm (p.γ₁ - p.β)]) (.block accAnd))

/-- `Â[r, s]`, entry `e = 8r + s`. -/
def aOne (e : Nat) : Prog isa :=
  .seq (.block (st8 (oSB + 32) (e % 8))) <| .seq (.block (st8 (oSB + 33) (e / 8))) <|
  .seq (callPR vS "vg_mldsa_rej_ntt_poly" P.rejNtt [.buf (sb oSB 34), .buf (pB (20 + e)), .buf (ssB 2048)])
    (maskA oACC (oP (20 + e)))

/-- The entries `8r + s` of row `r` of `Â`. -/
def aRow (r : Nat) : Prog isa := seqR (aOne P) (8 * r) p.ℓ

/-- `ρ` to the seed, `Â`, and `c`. -/
def samples : Prog isa :=
  .seq (copyW vS ⟨0, 0, 32⟩ (sb oSB 32) 8) <| .seq (seqR (aRow P p) 0 p.k) <|
  .seq (callPR vS "vg_mldsa_sample_in_ball" P.ball
      [.buf ⟨2, 0, p.ctildeLen⟩, .imm p.ctildeLen, .imm p.τ, .buf pC, .buf (ssB 2048)])
    (maskA oACC (oP 15))

/-- `f ← NTT(f)`. -/
def nttAt (f : Buf) : Prog isa := callP vS "vg_mldsa_ntt" P.ntt [.buf f, .buf (ssB 1024)]

/-- `w′ ← w′ + Â[r, s] ẑ[s]`. -/
def mulAddS (r s : Nat) : Prog isa :=
  callP vS "vg_mldsa_multiply_add_ntt" P.mulAdd [.buf pW, .buf (pA r s), .buf (pZ s)]

/-- Row `r` of `w′`, `w′₁`, packed to `oB`. -/
def row (r : Nat) : Prog isa :=
  .seq (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pW, .buf (pA r 0), .buf (pZ 0)]) <|
  .seq (seqR (mulAddS P r) 1 (p.ℓ - 1)) <|
  .seq (callP vS "vg_mldsa_unpack_t1" P.unpackT1 [.buf ⟨0, 32 + 320 * r, 320⟩, .buf pT]) <|
  .seq (nttAt P pT) <|
  .seq (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pT2, .buf pC, .buf pT]) <|
  .seq (callP vS "vg_mldsa_sub" P.sub [.buf pW, .buf pT2]) <|
  .seq (callP vS "vg_mldsa_inv_ntt" P.invNtt [.buf pW, .buf (ssB 1024)]) <|
  .seq (callP vS "vg_mldsa_use_hint" P.useHint [.buf (pB r), .buf pW, .imm p.γ₂, .buf pW1])
    (callP vS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf pW1, .imm (w1Max p), .buf (sb (oB + w1Len p * r) (w1Len p)), .imm (w1Len p)])

/-- The NTTs of `z` and `c`, the rows, the hash and the comparison. -/
def compute : Prog isa :=
  .seq (seqR (fun i => nttAt P (pZ i)) 0 p.ℓ) <| .seq (nttAt P pC) <| .seq (seqR (row P p) 0 p.k) <|
  .seq (hash2 vS 0 200 136 0x1f ⟨1, 0, 64⟩ (sb oB (p.k * w1Len p)) (sb oCT p.ctildeLen))
    (cmpAnd (sb oCT p.ctildeLen) ⟨2, 0, p.ctildeLen⟩ p.ctildeLen)

/-- The body: everything between the leaf's saves and restores. -/
def body : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))]) <| .seq (hint P p) <|
  .seq (ifOk (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) (compute P p)))))
    (.block [.mov .eax (.mem (at_ .esi oACC))])

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the primitives `P`. -/
def verify : Prog isa := leaf (body P p)

end

end VG.Impl.MlDsa.X86.Verify

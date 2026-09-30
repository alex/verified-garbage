import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Call
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

`keyGen P p (seed, pk, sk, scratch) -> eax`: `ML-DSA.KeyGen_internal(ξ)`
(FIPS 204 Algorithm 6) of the parameter set `p`, with `ξ` at `seed`, as calls
of the primitives `P` (`Prims`, any implementations of them) and of the
SHA-3 sponge functions. It is a leaf (`Impl.MlKem.X86.leaf`) that keeps
`scratch` (argument 3) in `esi`, as ML-KEM's top-level functions do, and the
AND of the results of the samplers in the word `oACC` of `scratch`.

The layout of `scratch` (in bytes): the Keccak state at 0 and the sponge
functions' working space at 200; `k` and `ℓ` at 896 (`oKL`); the AND of the
samplers' results at 900 (`oACC`); `(ρ, ρ′, K)` at 1024 (`oHX`, 128 bytes);
the seed of `RejNTTPoly` at 1152 (`oSA`, 34 bytes) and of `RejBoundedPoly`
at 1216 (`oSB`, 66 bytes); the working space of the primitives at 2048
(2048 bytes); and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]` is
polynomial `rℓ + s`, `s₁[j]` (then `ŝ₁[j]`) polynomial `kℓ + j`, `s₂[i]`
polynomial `kℓ + ℓ + i`, and `t`, `t₁` and `t₀` the three after them.

1. `oACC ← 1`; `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, and `ρ` and `ρ′` to the seeds.
2. `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` and `s₁ ‖ s₂ = RejBoundedPoly(ρ′ ‖ r ‖ 0)`
   (`ExpandA`, `ExpandS`). After each, `oACC ← oACC ∧ result`, and the
   polynomial is ANDed with `-result` (`maskA`): it is zero if the sampler
   failed, so that every polynomial is reduced, and small, whatever the
   samplers return, without a branch.
3. `ρ` to `pk` and `ρ` and `K` to `sk`; `s₁` and `s₂`, `BitPack`ed, to `sk`;
   `ŝ₁ = NTT(s₁)`.
4. For each row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, `Power2Round`,
   and `t₁` `SimpleBitPack`ed to `pk`, `t₀` `BitPack`ed to `sk`.
5. `tr = H(pk, 64)` to `sk`; return `oACC`.

Every address and branch depends only on the pointers, but for what the
samplers leak (`ρ` and which half-bytes `RejBoundedPoly` rejects).
-/

namespace VG.Impl.MlDsa.X86.KeyGen

open VG.X86
open VG.Impl.MlKem.X86 (Buf st8 copyW maskA hash1 hash2 leaf at_)
open VG.Spec.MlDsa (Params bitlen)

/-- The code of the primitives key generation calls. -/
structure Prims where
  /-- `vg_mldsa_ntt` -/
  ntt : Prog isa
  /-- `vg_mldsa_inv_ntt` -/
  invNtt : Prog isa
  /-- `vg_mldsa_multiply_ntt` -/
  mul : Prog isa
  /-- `vg_mldsa_multiply_add_ntt` -/
  mulAdd : Prog isa
  /-- `vg_mldsa_add` -/
  add : Prog isa
  /-- `vg_mldsa_rej_ntt_poly` -/
  rejNtt : Prog isa
  /-- `vg_mldsa_rej_bounded_poly` -/
  rejBounded : Prog isa
  /-- `vg_mldsa_power2round` -/
  power2Round : Prog isa
  /-- `vg_mldsa_simple_bit_pack` -/
  simpleBitPack : Prog isa
  /-- `vg_mldsa_bit_pack` -/
  bitPack : Prog isa

/-! ## The layout of the working space -/

/-- `scratch` is argument 3. -/
abbrev kS : Nat := 3
def oKL : Nat := 896
def oACC : Nat := 900
def oHX : Nat := 1024
def oSA : Nat := 1152
def oSB : Nat := 1216
def oSS : Nat := 2048
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 4096 + 1024 * j

/-- A buffer of `scratch`. -/
abbrev sb (o l : Nat) : Buf := ⟨kS, o, l⟩
/-- Polynomial `j` of `scratch`. -/
abbrev pB (j : Nat) : Buf := sb (oP j) 1024
/-- `Â[r, s]`, entry `e = rℓ + s`. -/
abbrev aB (e : Nat) : Buf := pB e
/-- `s₁ ‖ s₂`, entry `r`. -/
abbrev sB (p : Params) (r : Nat) : Buf := pB (p.k * p.ℓ + r)
abbrev tB (p : Params) : Buf := pB (p.k * p.ℓ + p.ℓ + p.k)
abbrev t1B (p : Params) : Buf := pB (p.k * p.ℓ + p.ℓ + p.k + 1)
abbrev t0B (p : Params) : Buf := pB (p.k * p.ℓ + p.ℓ + p.k + 2)
/-- The working space of the primitives: 1024 bytes for the NTTs, 2048 for the samplers. -/
abbrev ssB (l : Nat) : Buf := sb oSS l

/-- The length of a packed polynomial of `s₁` or `s₂`, `32 · bitlen (2η)`. -/
def lenS (p : Params) : Nat := 32 * bitlen (2 * p.η)
/-- Where `t₀` starts in `sk`. -/
def oT0 (p : Params) : Nat := 128 + lenS p * (p.ℓ + p.k)

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `oACC ← 1`; `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, `ρ` to the seed of
`RejNTTPoly`, and `ρ′ ‖ 0` to that of `RejBoundedPoly`. -/
def seeds : Prog isa :=
  .seq (.block [.mov .eax (.imm 1), .store (at_ .esi oACC) .eax]) <|
  .seq (.block (st8 oKL p.k)) <| .seq (.block (st8 (oKL + 1) p.ℓ)) <|
  .seq (hash2 kS 0 200 136 0x1f ⟨0, 0, 32⟩ (sb oKL 2) (sb oHX 128)) <|
  .seq (copyW kS (sb oHX 32) (sb oSA 32) 8) <|
  .seq (copyW kS (sb (oHX + 32) 64) (sb oSB 64) 16) (.block (st8 (oSB + 65) 0))

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, masked. -/
def expA (e : Nat) : Prog isa :=
  .seq (.block (st8 (oSA + 32) (e % p.ℓ))) <| .seq (.block (st8 (oSA + 33) (e / p.ℓ))) <|
  .seq (callPR kS "vg_mldsa_rej_ntt_poly" P.rejNtt [.buf (sb oSA 34), .buf (aB e), .buf (ssB 2048)])
    (maskA oACC (oP e))

/-- Entry `r` of `s₁ ‖ s₂`: `RejBoundedPoly(ρ′ ‖ r ‖ 0)`, masked. -/
def expS (r : Nat) : Prog isa :=
  .seq (.block (st8 (oSB + 64) r)) <|
  .seq (callPR kS "vg_mldsa_rej_bounded_poly" P.rejBounded
      [.buf (sb oSB 66), .imm p.η, .buf (sB p r), .buf (ssB 2048)])
    (maskA oACC (oP (p.k * p.ℓ + r)))

/-- `ρ` to `pk` and `sk`, and `K` to `sk`. -/
def copies : Prog isa :=
  .seq (copyW kS (sb oHX 32) ⟨1, 0, 32⟩ 8) <| .seq (copyW kS (sb oHX 32) ⟨2, 0, 32⟩ 8)
    (copyW kS (sb (oHX + 96) 32) ⟨2, 32, 32⟩ 8)

/-- Entry `r` of `s₁ ‖ s₂`, packed to `sk`. -/
def packS (r : Nat) : Prog isa :=
  callP kS "vg_mldsa_bit_pack" P.bitPack
    [.buf (sB p r), .imm p.η, .imm p.η, .buf ⟨2, 128 + lenS p * r, lenS p⟩, .imm (lenS p)]

/-- `ŝ₁[j] = NTT(s₁[j])`. -/
def nttS (j : Nat) : Prog isa := callP kS "vg_mldsa_ntt" P.ntt [.buf (sB p j), .buf (ssB 1024)]

/-- `t ← t + Â[i, j] ŝ₁[j]`. -/
def mulAddS (i j : Nat) : Prog isa :=
  callP kS "vg_mldsa_multiply_add_ntt" P.mulAdd [.buf (tB p), .buf (aB (p.ℓ * i + j)), .buf (sB p j)]

/-- Row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, and its `t₁` to `pk` and `t₀` to `sk`. -/
def row (i : Nat) : Prog isa :=
  .seq (callP kS "vg_mldsa_multiply_ntt" P.mul [.buf (tB p), .buf (aB (p.ℓ * i)), .buf (sB p 0)]) <|
  .seq (seqR (mulAddS P p i) 1 (p.ℓ - 1)) <|
  .seq (callP kS "vg_mldsa_inv_ntt" P.invNtt [.buf (tB p), .buf (ssB 1024)]) <|
  .seq (callP kS "vg_mldsa_add" P.add [.buf (tB p), .buf (sB p (p.ℓ + i))]) <|
  .seq (callP kS "vg_mldsa_power2round" P.power2Round [.buf (tB p), .buf (t1B p), .buf (t0B p)]) <|
  .seq (callP kS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf (t1B p), .imm 1023, .buf ⟨1, 32 + 320 * i, 320⟩, .imm 320])
    (callP kS "vg_mldsa_bit_pack" P.bitPack
      [.buf (t0B p), .imm 4095, .imm 4096, .buf ⟨2, oT0 p + 416 * i, 416⟩, .imm 416])

/-- `tr = H(pk, 64)` to `sk`. -/
def trHash : Prog isa := hash1 kS 0 200 136 0x1f ⟨1, 0, p.pkLen⟩ ⟨2, 64, 64⟩

/-- The body: everything between the leaf's saves and restores. -/
def body : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * kS)))]) <| .seq (seeds p) <|
  .seq (seqR (expA P p) 0 (p.k * p.ℓ)) <| .seq (seqR (expS P p) 0 (p.ℓ + p.k)) <|
  .seq (copies) <| .seq (seqR (packS P p) 0 (p.ℓ + p.k)) <| .seq (seqR (nttS P p) 0 p.ℓ) <|
  .seq (seqR (row P p) 0 p.k) <| .seq (trHash p) (.block [.mov .eax (.mem (at_ .esi oACC))])

/-- `vg_mldsa*_keygen` for the parameter set `p`, calling the primitives `P`. -/
def keyGen : Prog isa := leaf (body P p)

end

end VG.Impl.MlDsa.X86.KeyGen

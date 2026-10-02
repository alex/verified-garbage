import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Prims
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86-64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

`keyGen P p (seed = rdi, pk = rsi, sk = rdx, scratch = rcx) -> eax`:
`ML-DSA.KeyGen_internal(ξ)` (FIPS 204 Algorithm 6) of the parameter set
`p`, with `ξ` at `seed`, as calls of the primitives `P` and of the SHA-3
sponge functions. Like ML-KEM's top-level functions
(`Impl/MlKem/X86_64/Frag.lean`, whose pieces it uses), it keeps `scratch` in
`rbx`, `seed` in `rbp`, `pk` in `r12` and `sk` in `r13`, and the AND of the
results of the samplers in `r15`, and saves its caller's values of them
(and of `r14`) in `scratch`.

The layout of `scratch` (in bytes): the Keccak state at 0 and the sponge
functions' working space at 200, the saved registers at 840 (as ML-KEM's);
`k` and `ℓ` at 896 (`oKL`); `(ρ, ρ′, K)` at 1024 (`oHX`, 128 bytes); the
seed of `RejNTTPoly` at 1152 (`oSA`, 34 bytes) and of `RejBoundedPoly` at
1216 (`oSB`, 66 bytes); the four seeds of `vg_mldsa_rej_ntt_poly4` at 1408
(`oSA4`, 136 bytes); the working space of the primitives at 2048
(2048 bytes); and polynomials of 1024 bytes from 4096 (`oP j`): `Â[r, s]`
is polynomial `rℓ + s`, `s₁[j]` (then `ŝ₁[j]`) polynomial `kℓ + j`,
`s₂[i]` polynomial `kℓ + ℓ + i`, and `t`, `t₁` and `t₀` the three after
them; then the working space of `vg_mldsa_rej_ntt_poly4` (8 KiB, `oR4`).

1. `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, and `ρ` and `ρ′` to the seeds.
2. `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)`, four consecutive entries at a time
   (`vg_mldsa_rej_ntt_poly4`, from the seeds at `oSA4`, each `ρ` with its
   entry's indices) and the last `kℓ mod 4` one at a time, and
   `s₁ ‖ s₂ = RejBoundedPoly(ρ′ ‖ r ‖ 0)` (`ExpandA`, `ExpandS`). After each
   call, `r15 ← r15 ∧ result`, and the polynomials it sampled are ANDed with
   `-result` (`mask`): they are zero if the sampler failed, so that every
   polynomial is reduced, and small, whatever the samplers return, without a
   branch.
3. `ρ` and `K` to `sk`; `s₁` and `s₂`, `BitPack`ed, to `sk`; `ŝ₁ = NTT(s₁)`.
4. For each row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, `Power2Round`, and
   `t₁` `SimpleBitPack`ed to `pk`, `t₀` `BitPack`ed to `sk`; `ρ` to `pk`.
5. `tr = H(pk, 64)` to `sk`; return `r15`.

Every address and branch depends only on the pointers, but for what the
samplers leak (`ρ` and which half-bytes `RejBoundedPoly` rejects).
-/

namespace VG.Impl.MlDsa.X86_64.KeyGen

open VG.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc lea setB copy hashAt seqR topPro topEpi at_ oSS)
open VG.Spec.MlDsa (Params bitlen)

/-! ## The layout of the working space -/

def oKL : Nat := 896
def oHX : Nat := 1024
def oSA : Nat := 1152
def oSB : Nat := 1216
def oSA4 : Nat := 1408
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 4096 + 1024 * j

/-- `Â[r, s]`, entry `e = rℓ + s`. -/
abbrev aP (e : Nat) : Ptr := sc (oP e)
/-- `s₁ ‖ s₂`, entry `r`. -/
abbrev sP (p : Params) (r : Nat) : Ptr := sc (oP (p.k * p.ℓ + r))
abbrev tP (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k))
abbrev t1P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 1))
abbrev t0P (p : Params) : Ptr := sc (oP (p.k * p.ℓ + p.ℓ + p.k + 2))
/-- The working space of `vg_mldsa_rej_ntt_poly4`. -/
def oR4 (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k + 3)

/-- The length of a packed polynomial of `s₁` or `s₂`, `32 · bitlen (2η)`. -/
def lenS (p : Params) : Nat := 32 * bitlen (2 * p.η)
/-- Where `t₀` starts in `sk`. -/
def oT0 (p : Params) : Nat := 128 + lenS p * (p.ℓ + p.k)

/-! ## Calls of the primitives -/

/-- `r ← v`, a 32-bit immediate. -/
def imm (r : Reg) (v : Nat) : List Instr := [.mov32 r (.imm (BitVec.ofNat 32 v))]

def nttAt (sfx : String) (c : Prog isa) (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call ("vg_mldsa_ntt" ++ sfx) c)

def invNttAt (sfx : String) (c : Prog isa) (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call ("vg_mldsa_inv_ntt" ++ sfx) c)

def mulAt (sfx : String) (c : Prog isa) (h f g : Ptr) : Prog isa :=
  .seq (.block (lea .rdi h ++ lea .rsi f ++ lea .rdx g)) (.call ("vg_mldsa_multiply_ntt" ++ sfx) c)

def mulAddAt (sfx : String) (c : Prog isa) (h f g : Ptr) : Prog isa :=
  .seq (.block (lea .rdi h ++ lea .rsi f ++ lea .rdx g)) (.call ("vg_mldsa_multiply_add_ntt" ++ sfx) c)

def addAt (sfx : String) (c : Prog isa) (f g : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ lea .rsi g)) (.call ("vg_mldsa_add" ++ sfx) c)

def rejNttAt (c : Prog isa) (seed a : Ptr) : Prog isa :=
  .seq (.block (lea .rdi seed ++ lea .rsi a ++ lea .rdx (sc oSS))) (.call "vg_mldsa_rej_ntt_poly" c)

def rej4At (c : Prog isa) (sfx : String) (a w : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc oSA4) ++ lea .rsi a ++ lea .rdx w)) (.call ("vg_mldsa_rej_ntt_poly4" ++ sfx) c)

def rejBoundedAt (c : Prog isa) (seed : Ptr) (eta : Nat) (a : Ptr) : Prog isa :=
  .seq (.block (lea .rdi seed ++ imm .rsi eta ++ lea .rdx a ++ lea .rcx (sc oSS)))
    (.call "vg_mldsa_rej_bounded_poly" c)

def power2RoundAt (c : Prog isa) (t t1 t0 : Ptr) : Prog isa :=
  .seq (.block (lea .rdi t ++ lea .rsi t1 ++ lea .rdx t0)) (.call "vg_mldsa_power2round" c)

def simpleBitPackAt (c : Prog isa) (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  .seq (.block (lea .rdi f ++ imm .rsi b ++ lea .rdx out ++ imm .rcx len))
    (.call "vg_mldsa_simple_bit_pack" c)

def bitPackAt (c : Prog isa) (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  .seq (.block (lea .rdi f ++ imm .rsi a ++ imm .rdx b ++ lea .rcx out ++ imm .r8 len))
    (.call "vg_mldsa_bit_pack" c)

/-- `r15 ← r15 ∧ eax`, and the polynomial at `a` (or the `N` coefficients from `a`) ANDed with `-eax`
(`eax` is 0 or 1). -/
def mask (a : Ptr) (N : Nat := 256) : Prog isa :=
  .seq (.block ([.alu32 .and .r15 (.reg .rax), .mov32 .r8 (.imm 0), .alu32 .sub .r8 (.reg .rax)] ++
      lea .rdi a ++ imm .rcx N))
    (.loop (.block [.mov32 .rax (.mem (at_ .rdi 0)), .alu32 .and .rax (.reg .r8), .store32 (at_ .rdi 0) .rax,
      .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) .ne)

/-! ## The pieces -/

def pro : List Instr := topPro .rcx [(.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]

/-- `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, `ρ` to the seed of `RejNTTPoly`, and
`ρ′ ‖ 0` to that of `RejBoundedPoly`. -/
def seeds (p : Params) : Prog isa :=
  .seq (.block (setB (sc oKL) p.k ++ setB (sc (oKL + 1)) p.ℓ))
    (.seq (hashAt [((.rbp, 0), 32), (sc oKL, 2)] 136 0x1f (sc oHX) 128)
      (.seq (copy (sc oSA) (sc oHX) 32) (.seq (copy (sc oSB) (sc (oHX + 32)) 64) (.seq (.block (setB (sc (oSB + 65)) 0))
        (.seq (copy (sc oSA4) (sc oHX) 32) (.seq (copy (sc (oSA4 + 34)) (sc oHX) 32)
          (.seq (copy (sc (oSA4 + 68)) (sc oHX) 32) (copy (sc (oSA4 + 102)) (sc oHX) 32))))))))

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`. -/
def expA (P : Prims) (p : Params) (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ)))
    (.seq (rejNttAt P.rejNtt (sc oSA) (aP e)) (mask (aP e)))

/-- The indices of entry `e + k` of `Â` to seed `k` of `oSA4`. -/
def setSR (p : Params) (e k : Nat) : List Instr :=
  setB (sc (oSA4 + 34 * k + 32)) ((e + k) % p.ℓ) ++ setB (sc (oSA4 + 34 * k + 32 + 1)) ((e + k) / p.ℓ)

/-- Entries `4g, …, 4g + 3` of `Â`. -/
def expA4 (P : Prims) (p : Params) (g : Nat) : Prog isa :=
  .seq (.block (setSR p (4 * g) 0)) (.seq (.block (setSR p (4 * g) 1)) (.seq (.block (setSR p (4 * g) 2))
    (.seq (.block (setSR p (4 * g) 3)) (.seq (rej4At P.rej4 P.sfx (aP (4 * g)) (sc (oR4 p))) (mask (aP (4 * g)) 1024)))))

/-- The entries of `Â`: four at a time, then the last `kℓ mod 4` one at a time. -/
def expAll (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (expA4 P p) 0 (p.k * p.ℓ / 4)) (seqR (expA P p) (4 * (p.k * p.ℓ / 4)) (p.k * p.ℓ % 4))

/-- Entry `r` of `s₁ ‖ s₂`: `RejBoundedPoly(ρ′ ‖ r ‖ 0)`. -/
def expS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 64)) r))
    (.seq (rejBoundedAt P.rejBounded (sc oSB) p.η (sP p r)) (mask (sP p r)))

/-- `ρ` to `pk` and `sk`, and `K` to `sk`. -/
def copies : Prog isa :=
  .seq (copy (.r12, 0) (sc oHX) 32) (.seq (copy (.r13, 0) (sc oHX) 32) (copy (.r13, 32) (sc (oHX + 96)) 32))

/-- Entry `r` of `s₁ ‖ s₂`, packed to `sk`. -/
def packS (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  bitPackAt P.bitPack (sP p r) p.η p.η (.r13, 128 + lenS p * r) (lenS p)

/-- `ŝ₁[j] = NTT(s₁[j])`. -/
def nttS (P : Prims) (p : Params) (j : Nat) : Prog isa := nttAt P.sfx P.ntt (sP p j)

/-- Row `i`: `t = NTT⁻¹(Σⱼ Â[i, j] ŝ₁[j]) + s₂[i]`, and its `t₁` to `pk` and `t₀` to `sk`. -/
def row (P : Prims) (p : Params) (i : Nat) : Prog isa :=
  .seq (mulAt P.sfx P.mul (tP p) (aP (p.ℓ * i)) (sP p 0))
    (.seq (seqR (fun j => mulAddAt P.sfx P.mulAdd (tP p) (aP (p.ℓ * i + j)) (sP p j)) 1 (p.ℓ - 1))
    (.seq (invNttAt P.sfx P.invNtt (tP p)) (.seq (addAt P.sfx P.add (tP p) (sP p (p.ℓ + i)))
    (.seq (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p))
    (.seq (simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320)
      (bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416))))))

/-- `tr = H(pk, 64)` to `sk`. -/
def trHash (p : Params) : Prog isa := hashAt [((.r12, 0), p.pkLen)] 136 0x1f (.r13, 64) 64

/-- Everything after the samplers. -/
def rest (P : Prims) (p : Params) : Prog isa :=
  .seq copies (.seq (seqR (packS P p) 0 (p.ℓ + p.k)) (.seq (seqR (nttS P p) 0 p.ℓ)
    (.seq (seqR (row P p) 0 p.k) (trHash p))))

/-- `vg_mldsa*_keygen` for the parameter set `p`, calling the primitives `P`. -/
def keyGen (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (seeds p) (.seq (expAll P p)
    (.seq (seqR (expS P p) 0 (p.ℓ + p.k)) (.seq (rest P p) (.block topEpi)))))

end VG.Impl.MlDsa.X86_64.KeyGen

import VerifiedGarbage.Impl.MlKem.X86_64.Frag

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`

`keyGen(seed = rdi, ek = rsi, dk = rdx, scratch = rcx) -> eax`:
`ML-KEM.KeyGen_internal(d, z)` (FIPS 203 Algorithms 16 and 13) with
`d ‖ z` at `seed`, as calls of the verified primitives and sponge functions
(`Frag.lean`). It keeps `scratch` in `rbx`, `seed` in `rbp`, `ek` in `r12`
and `dk` in `r13`, and the AND of the results of `vg_mlkem_sample_ntt` in
`r15`, and saves its caller's values of them (and of `r14`) in `scratch`.

1. `(ρ, σ) = G(d ‖ 3)` to `G`, and `ρ` to `SB`, the seed of `SampleNTT`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the nine `(i, j)`, to polynomials
   6–14. If one of them failed (`r15 = 0`), it returns 0 at once.
3. `PRF₂(σ, N)` for `N = 0, …, 5` (`c.prfs`, to `PR`), and `ŝ[j]`
   (polynomial `j`) and `ê[i]` (polynomial `3 + i`):
   `NTT(SamplePolyCBD₂(PRF₂(σ, N)))`.
4. `t̂[i] = Â[i, 0] ŝ[0] + Â[i, 1] ŝ[1] + Â[i, 2] ŝ[2] + ê[i]` (polynomial 15),
   and `ByteEncode₁₂(t̂[i])` to `ek`; `ByteEncode₁₂(ŝ[j])` to `dk`.
5. `ρ` to `ek`, `ek` to `dk`, `H(ek)` to `dk`, and `z` to `dk`.

Only the calls of `vg_mlkem_sample_ntt`, and the branch on their results,
depend on `ρ` (which the contract declares that the function may leak);
every other address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace KeyGen

def pro : List Instr := topPro .rcx [(.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]

/-- `G(d ‖ 3)`, and `ρ` to `SB`. -/
def gRho : Prog isa :=
  .seq (.block (setB (sc oNB) 3)) (.seq (hashAt [((.rbp, 0), 32), (sc oNB, 1)] 72 6 (sc oG) 64)
    (copy (sc oSB) (sc oG) 32))

/-- `ŝ[N]` or `ê[N - 3]`, from `PRF₂(σ, N)`. -/
def se (N : Nat) : Prog isa := .seq (cbd2At (sc (oPR + 128 * N)) (pS N)) (nttAt (pS N))

/-- `t̂[i]`, encoded to `ek`. -/
def row (i : Nat) : Prog isa :=
  .seq (dotAt (fun j => aS i j) pS) (.seq (addAt (pS 15) (pS (3 + i))) (enc12At (pS 15) (.r12, 384 * i)))

/-- `ŝ[j]`, encoded to `dk`. -/
def encS (j : Nat) : Prog isa := enc12At (pS j) (.r13, 384 * j)

/-- `ρ` to `ek`, `ek` to `dk`, `H(ek)` and `z` to `dk`. -/
def fin : Prog isa :=
  .seq (copy (.r12, 1152) (sc oG) 32) (.seq (copy (.r13, 1152) (.r12, 0) 1184)
    (.seq (hashAt [((.r12, 0), 1184)] 136 6 (.r13, 2336) 32) (copy (.r13, 2368) (.rbp, 32) 32)))

def rest (c : Callee4) : Prog isa :=
  .seq (c.prfs 0 6 oPR lPW) (.seq (seqR se 0 6) (.seq (seqR row 0 3) (.seq (seqR encS 0 3) fin)))

end KeyGen

open KeyGen in
def keyGen (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq gRho (.seq (samples c) (.seq (ifOk (rest c)) (.block topEpi))))

end VG.Impl.MlKem.X86_64

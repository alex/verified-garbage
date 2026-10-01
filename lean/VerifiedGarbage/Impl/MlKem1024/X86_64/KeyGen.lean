import VerifiedGarbage.Impl.MlKem1024.X86_64.Frag

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen`

`keyGen1024(seed = rdi, ek = rsi, dk = rdx, scratch = rcx) -> eax`:
`ML-KEM.KeyGen_internal(d, z)` (FIPS 203 Algorithms 16 and 13) of
ML-KEM-1024, as `vg_mlkem768_keygen` (`Impl/MlKem/X86_64/KeyGen.lean`)
with `k = 4`: the same registers and saves.

1. `(ρ, σ) = G(d ‖ 4)` to `G`, and `ρ` to `SB`, the seed of `SampleNTT`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the sixteen `(i, j)`, to polynomials
   17–32. If one of them failed (`r15 = 0`), it returns 0 at once.
3. `PRF₂(σ, N)` for `N = 0, …, 7` (`c.prfs`, to `PR4`), and `ŝ[j]`
   (polynomial `j`) and `ê[i]` (polynomial `4 + i`):
   `NTT(SamplePolyCBD₂(PRF₂(σ, N)))`.
4. `t̂[i] = Â[i, 0] ŝ[0] + ⋯ + Â[i, 3] ŝ[3] + ê[i]` (polynomial 15), and
   `ByteEncode₁₂(t̂[i])` to `ek`; `ByteEncode₁₂(ŝ[j])` to `dk`.
5. `ρ` to `ek`, `ek` to `dk`, `H(ek)` to `dk`, and `z` to `dk`.

Only the calls of `vg_mlkem_sample_ntt`, and the branch on their results,
depend on `ρ` (which the contract declares that the function may leak);
every other address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

namespace KeyGen1024

def pro : List Instr := topPro .rcx [(.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]

/-- `G(d ‖ 4)`, and `ρ` to `SB`. -/
def gRho : Prog isa :=
  .seq (.block (setB (sc oNB) 4)) (.seq (hashAt [((.rbp, 0), 32), (sc oNB, 1)] 72 6 (sc oG) 64)
    (copy (sc oSB) (sc oG) 32))

/-- `ŝ[N]` or `ê[N - 4]`. -/
def se (A : Arith) (N : Nat) : Prog isa := .seq (cbd2At (sc (oPR4 + 128 * N)) (pS N)) (nttAt A (pS N))

/-- `t̂[i]`, encoded to `ek`. -/
def row (A : Arith) (i : Nat) : Prog isa :=
  .seq (dot4At A (fun j => aS4 i j) pS) (.seq (addAt (pS 15) (pS (4 + i))) (enc12At (pS 15) (.r12, 384 * i)))

/-- `ŝ[j]`, encoded to `dk`. -/
def encS (j : Nat) : Prog isa := enc12At (pS j) (.r13, 384 * j)

/-- `ρ` to `ek`, `ek` to `dk`, `H(ek)` and `z` to `dk`. -/
def fin : Prog isa :=
  .seq (copy (.r12, 1536) (sc oG) 32) (.seq (copy (.r13, 1536) (.r12, 0) 1568)
    (.seq (hashAt [((.r12, 0), 1568)] 136 6 (.r13, 3104) 32) (copy (.r13, 3136) (.rbp, 32) 32)))

def rest (c : Callee4) : Prog isa :=
  .seq (c.prfs 0 8 oPR4 lPW4) (.seq (seqR (se c.arith) 0 8) (.seq (seqR (row c.arith) 0 4) (.seq (seqR encS 0 4) fin)))

end KeyGen1024

open KeyGen1024 in
def keyGen1024 (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq gRho (.seq (samples4 c) (.seq (ifOk (rest c)) (.block topEpi))))

end VG.Impl.MlKem1024.X86_64

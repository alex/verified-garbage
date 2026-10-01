import VerifiedGarbage.Impl.MlKem1024.X86_64.Frag

/-!
# ML-KEM-1024 on x86-64: K-PKE.Encrypt, in `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps`

`K-PKE.Encrypt(ek, m, r)` (FIPS 203 Algorithm 14) of ML-KEM-1024, as that
of ML-KEM-768 (`Impl/MlKem/X86_64/Encrypt.lean`) with `k = 4`, `d_u = 11`
and `d_v = 5`: the encryption key `ek` at the pointer `E` (`r14` in
`vg_mlkem1024_encaps`, `rbp + 1536` in `vg_mlkem1024_decaps`), the message
`m` at `M` and the randomness `r` at `G + 32`; the ciphertext to `CT` in
`scratch` (1568 bytes, polynomials 33 and 34). `r15` is the AND of the
results of `vg_mlkem_sample_ntt`.

1. `ρ` (`ek[1536 : 1568]`) to `SB`; `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` to
   polynomials 17–32. If one of them failed (`r15 = 0`), nothing more.
2. `PRF₂(r, N)` for `N = 0, …, 8` (`c.prfs`, to `PR4`), and
   `ŷ[j] = NTT(SamplePolyCBD₂(PRF₂(r, j)))` (polynomial `j`).
3. `u[i] = NTT⁻¹(Â[0, i] ŷ[0] + ⋯ + Â[3, i] ŷ[3]) + e₁[i]` (polynomial
   15), with `e₁[i] = SamplePolyCBD₂(PRF₂(r, 4 + i))` (polynomial 16), and
   `ByteEncode₁₁(Compress₁₁(u[i]))` to `CT + 352i`.
4. `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (polynomial `4 + i`);
   `v = NTT⁻¹(t̂[0] ŷ[0] + ⋯ + t̂[3] ŷ[3]) + e₂ + μ` (polynomial 15), with
   `e₂ = SamplePolyCBD₂(PRF₂(r, 8))` and `μ = Decompress₁(ByteDecode₁(m))`,
   and `ByteEncode₅(Compress₅(v))` to `CT + 1408`.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

namespace Encrypt1024

/-- `PRF₂(r, N)`. -/
abbrev prfO (N : Nat) : Ptr := sc (oPR4 + 128 * N)

/-- `ρ` to `SB`, and `Â`. -/
def mat (c : Callee4) (E : Ptr) : Prog isa := .seq (copy (sc oSB) (E.1, E.2 + 1536) 32) (samples4 c)

/-- `ŷ[j]`. -/
def y (j : Nat) : Prog isa := .seq (cbd2At (prfO j) (pS j)) (nttAt (pS j))

/-- `u[i]`, compressed and encoded to the ciphertext. -/
def u (i : Nat) : Prog isa :=
  .seq (dot4At (fun j => aS4 j i) pS) (.seq (nttInvAt (pS 15)) (.seq (cbd2At (prfO (4 + i)) (pS 16))
    (.seq (addAt (pS 15) (pS 16)) (ce4At (pS 15) 11 (sc (oCT4 + 352 * i))))))

/-- `t̂[i]`. -/
def t (E : Ptr) (i : Nat) : Prog isa := dec12At (E.1, E.2 + 384 * i) (pS (4 + i))

/-- `v`, compressed and encoded to the ciphertext. -/
def v : Prog isa :=
  .seq (dot4At (fun j => pS (4 + j)) pS) (.seq (nttInvAt (pS 15)) (.seq (cbd2At (prfO 8) (pS 16))
    (.seq (addAt (pS 15) (pS 16)) (.seq (ddAt (sc oM) 1 (pS 16)) (.seq (addAt (pS 15) (pS 16))
      (ce4At (pS 15) 5 (sc (oCT4 + 1408))))))))

def rest (c : Callee4) (E : Ptr) : Prog isa :=
  .seq (c.prfs 0 9 oPR4 lPW4) (.seq (seqR y 0 4) (.seq (seqR u 0 4) (.seq (seqR (t E) 0 4) v)))

end Encrypt1024

open Encrypt1024 in
def encrypt1024 (c : Callee4) (E : Ptr) : Prog isa := .seq (mat c E) (ifOk (rest c E))

end VG.Impl.MlKem1024.X86_64

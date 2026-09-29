import VerifiedGarbage.Impl.MlKem.X86_64.Frag

/-!
# ML-KEM-768 on x86-64: K-PKE.Encrypt, in `vg_mlkem768_encaps` and `vg_mlkem768_decaps`

`K-PKE.Encrypt(ek, m, r)` (FIPS 203 Algorithm 14) with the encryption key
`ek` at `r14`, the message `m` at `M` and the randomness `r` at `G + 32`
(the second half of `G`'s output) in the working space `scratch` at `rbx`:
the ciphertext to `CT` in `scratch` (1088 bytes). `r15` is the AND of the
results of `vg_mlkem_sample_ntt`, as in `vg_mlkem768_keygen`.

1. `ρ` (`ek[1152 : 1184]`) to `SB`; `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` to
   polynomials 6–14. If one of them failed (`r15 = 0`), nothing more.
2. `ŷ[j] = NTT(SamplePolyCBD₂(PRF₂(r, j)))` (polynomial `j`).
3. `u[i] = NTT⁻¹(Â[0, i] ŷ[0] + Â[1, i] ŷ[1] + Â[2, i] ŷ[2]) + e₁[i]`
   (polynomial 15), with `e₁[i] = SamplePolyCBD₂(PRF₂(r, 3 + i))`
   (polynomial 16), and `ByteEncode₁₀(Compress₁₀(u[i]))` to `CT + 320i`.
4. `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (polynomial `3 + i`);
   `v = NTT⁻¹(t̂[0] ŷ[0] + t̂[1] ŷ[1] + t̂[2] ŷ[2]) + e₂ + μ` (polynomial 15),
   with `e₂ = SamplePolyCBD₂(PRF₂(r, 6))` and
   `μ = Decompress₁(ByteDecode₁(m))`, and `ByteEncode₄(Compress₄(v))` to
   `CT + 960`.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Encrypt

/-- `r`. -/
abbrev rP : Ptr := sc (oG + 32)

/-- `ρ` to `SB`, and `Â`. -/
def mat : Prog isa := .seq (copy (sc oSB) (.r14, 1152) 32) samples

/-- `ŷ[j]`. -/
def y (j : Nat) : Prog isa := .seq (prfCbd rP j (pS j)) (nttAt (pS j))

/-- `u[i]`, compressed and encoded to the ciphertext. -/
def u (i : Nat) : Prog isa :=
  .seq (dotAt (fun j => aS j i) pS) (.seq (nttInvAt (pS 15)) (.seq (prfCbd rP (3 + i) (pS 16))
    (.seq (addAt (pS 15) (pS 16)) (ceAt (pS 15) 10 (sc (oCT + 320 * i))))))

/-- `t̂[i]`. -/
def t (i : Nat) : Prog isa := dec12At (.r14, 384 * i) (pS (3 + i))

/-- `v`, compressed and encoded to the ciphertext. -/
def v : Prog isa :=
  .seq (dotAt (fun j => pS (3 + j)) pS) (.seq (nttInvAt (pS 15)) (.seq (prfCbd rP 6 (pS 16))
    (.seq (addAt (pS 15) (pS 16)) (.seq (ddAt (sc oM) 1 (pS 16)) (.seq (addAt (pS 15) (pS 16))
      (ceAt (pS 15) 4 (sc (oCT + 960))))))))

def rest : Prog isa := .seq (seqR y 0 3) (.seq (seqR u 0 3) (.seq (seqR t 0 3) v))

end Encrypt

open Encrypt in
def encrypt : Prog isa := .seq mat (ifOk rest)

end VG.Impl.MlKem.X86_64

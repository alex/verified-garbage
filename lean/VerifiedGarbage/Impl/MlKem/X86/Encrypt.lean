import VerifiedGarbage.Impl.MlKem.X86.Top

/-!
# ML-KEM-768 on x86 (32-bit): K-PKE.Encrypt, in `scratch`

`encrypt sc`: K-PKE.Encrypt(ek, m, r) (Algorithm 14), with every buffer in
`scratch` (argument `sc`, in `esi`), at these offsets, which
`vg_mlkem768_encaps` and `vg_mlkem768_decaps` share:

* `[0, 3072)`: `ŷ[0]`, `ŷ[1]`, `ŷ[2]`, 1024 bytes each;
* `eE`: `e₁[i]` or `e₂`; `eU`: `u[i]`, then `v`, as it is summed; `eA`:
  `Â[j, i]`; `eP`: a product; `eT`: `t̂[j]`; `eMU`: `μ`;
* `eNS`: the scratch of the NTT and of the products; `eSS`: that of
  `vg_mlkem_sample_ntt`; `eST`, `eWK`: the Keccak state and working space;
* `ePRF`: the output of `PRF`; `eACC`: the AND of the values
  `vg_mlkem_sample_ntt` returned (set to 1 first);
* `eEK`: `ek` (1184 bytes), then `i` and `j`, so that `ρ ‖ i ‖ j` (the seed of
  `Â[j, i]`) is at `eEK + 1152`;
* `eM`: `m`; `eKR`: 64 bytes whose last 32 are `r`, then the `N` of
  `PRF(r, N)`, so that `r ‖ N` is at `eKR + 32`;
* `eC`: the ciphertext (1088 bytes).

The code is unrolled: `ŷ[N]` is `encYC N` (`PRF`, CBD, NTT); `u[i]` is
`encRow i`: the entries `Â[j, i]` for `j < 3`, each sampled, masked and
multiplied by `ŷ[j]` and summed (`encEntry`), then `NTT⁻¹`, `e₁[i]` added and
the sum compressed into the ciphertext; and `v` is `encV`: the products of
`t̂[j]` (decoded from `ek`) and `ŷ[j]` summed, `NTT⁻¹`, `e₂` and `μ` added, and
the sum compressed into the ciphertext.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

def eE : Nat := 3072
def eU : Nat := 4096
def eA : Nat := 5120
def eP : Nat := 6144
def eT : Nat := 7168
def eMU : Nat := 8192
def eNS : Nat := 9216
def eSS : Nat := 10240
def eST : Nat := 12288
def eWK : Nat := 12488
def ePRF : Nat := 13128
def eACC : Nat := 13256
def eEK : Nat := 13260
def eM : Nat := 14448
def eKR : Nat := 14480
def eC : Nat := 14548

/-- `SamplePolyCBD₂(PRF₂(r, N))` into `scratch + o`. -/
def encCbd (sc N o : Nat) : Prog isa :=
  .seq (.block (st8 (eKR + 64) N)) <|
  .seq (hash1 sc eST eWK 136 0x1f ⟨sc, eKR + 32, 33⟩ ⟨sc, ePRF, 128⟩) (cbd2C sc ⟨sc, ePRF, 128⟩ ⟨sc, o, 1024⟩)

/-- `ŷ[N] = NTT(SamplePolyCBD₂(PRF₂(r, N)))`. -/
def encYC (sc N : Nat) : Prog isa :=
  .seq (encCbd sc N (1024 * N)) (nttC sc ⟨sc, 1024 * N, 1024⟩ ⟨sc, eNS, 1024⟩)

/-- `Â[j, i] ← SampleNTT(ρ ‖ i ‖ j)`, masked, times `ŷ[j]`, added to `u[i]`
(written to it if `j = 0`). -/
def encEntry (sc i j : Nat) : Prog isa :=
  .seq (.block (st8 (eEK + 1184) i)) <| .seq (.block (st8 (eEK + 1185) j)) <|
  .seq (sampleC sc ⟨sc, eEK + 1152, 34⟩ ⟨sc, eA, 1024⟩ ⟨sc, eSS, 2048⟩) <|
  .seq (maskA eACC eA) <|
  if j = 0 then mulC sc ⟨sc, eU, 1024⟩ ⟨sc, eA, 1024⟩ ⟨sc, 0, 1024⟩ ⟨sc, eNS, 1024⟩
  else .seq (mulC sc ⟨sc, eP, 1024⟩ ⟨sc, eA, 1024⟩ ⟨sc, 1024 * j, 1024⟩ ⟨sc, eNS, 1024⟩)
    (addC sc ⟨sc, eU, 1024⟩ ⟨sc, eP, 1024⟩)

/-- `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, compressed into `c[320i : 320i + 320]`. -/
def encRow (sc i : Nat) : Prog isa :=
  .seq (encEntry sc i 0) <| .seq (encEntry sc i 1) <| .seq (encEntry sc i 2) <|
  .seq (nttInvC sc ⟨sc, eU, 1024⟩ ⟨sc, eNS, 1024⟩) <| .seq (encCbd sc (3 + i) eE) <|
  .seq (addC sc ⟨sc, eU, 1024⟩ ⟨sc, eE, 1024⟩) (ceC sc 10 ⟨sc, eU, 1024⟩ ⟨sc, eC + 320 * i, 320⟩)

/-- `t̂[j] ← ByteDecode₁₂(ek[384j : 384j + 384])`, times `ŷ[j]`, added to `v`
(written to it if `j = 0`). -/
def encTerm (sc j : Nat) : Prog isa :=
  .seq (dec12C sc ⟨sc, eEK + 384 * j, 384⟩ ⟨sc, eT, 1024⟩) <|
  if j = 0 then mulC sc ⟨sc, eU, 1024⟩ ⟨sc, eT, 1024⟩ ⟨sc, 0, 1024⟩ ⟨sc, eNS, 1024⟩
  else .seq (mulC sc ⟨sc, eP, 1024⟩ ⟨sc, eT, 1024⟩ ⟨sc, 1024 * j, 1024⟩ ⟨sc, eNS, 1024⟩)
    (addC sc ⟨sc, eU, 1024⟩ ⟨sc, eP, 1024⟩)

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + μ`, compressed into `c[960 : 1088]`. -/
def encV (sc : Nat) : Prog isa :=
  .seq (encTerm sc 0) <| .seq (encTerm sc 1) <| .seq (encTerm sc 2) <|
  .seq (nttInvC sc ⟨sc, eU, 1024⟩ ⟨sc, eNS, 1024⟩) <| .seq (encCbd sc 6 eE) <|
  .seq (addC sc ⟨sc, eU, 1024⟩ ⟨sc, eE, 1024⟩) <|
  .seq (ddC sc 1 ⟨sc, eM, 32⟩ ⟨sc, eMU, 1024⟩) <| .seq (addC sc ⟨sc, eU, 1024⟩ ⟨sc, eMU, 1024⟩)
    (ceC sc 4 ⟨sc, eU, 1024⟩ ⟨sc, eC + 960, 128⟩)

/-- K-PKE.Encrypt(ek, m, r), with `ek`, `m` and `r` in `scratch`, the ciphertext into it. -/
def encrypt (sc : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm 1), .store (at_ .esi eACC) .eax]) <|
  .seq (encYC sc 0) <| .seq (encYC sc 1) <| .seq (encYC sc 2) <|
  .seq (encRow sc 0) <| .seq (encRow sc 1) <| .seq (encRow sc 2) (encV sc)

end VG.Impl.MlKem.X86

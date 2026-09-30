import VerifiedGarbage.Impl.MlKem1024.X86.Top

/-!
# ML-KEM-1024 on x86 (32-bit): K-PKE.Encrypt, in `scratch`

`encrypt sc`: K-PKE.Encrypt(ek, m, r) (Algorithm 14) of ML-KEM-1024, as
ML-KEM-768's (`Impl/MlKem/X86/Encrypt.lean`) for `k = 4`, `d_u = 11` and
`d_v = 5`, with every buffer in `scratch` (argument `sc`, in `esi`), at these
offsets, which `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps` share:

* `[0, 4096)`: `ŷ[0]` … `ŷ[3]`, 1024 bytes each;
* `e4E`: `e₁[i]` or `e₂`; `e4U`: `u[i]`, then `v`, as it is summed; `e4A`:
  `Â[j, i]`; `e4P`: a product; `e4T`: `t̂[j]`; `e4MU`: `μ`;
* `e4NS`: the scratch of the NTT and of the products; `e4SS`: that of
  `vg_mlkem_sample_ntt`; `e4ST`, `e4WK`: the Keccak state and working space;
* `e4PRF`: the output of `PRF`; `e4ACC`: the AND of the values
  `vg_mlkem_sample_ntt` returned (set to 1 first);
* `e4EK`: `ek` (1568 bytes), then `i` and `j`, so that `ρ ‖ i ‖ j` (the seed
  of `Â[j, i]`) is at `e4EK + 1536`;
* `e4M`: `m`; `e4KR`: 64 bytes whose last 32 are `r`, then the `N` of
  `PRF(r, N)`, so that `r ‖ N` is at `e4KR + 32`;
* `e4C`: the ciphertext (1568 bytes).

The code is unrolled: `ŷ[N]` is `enc4YC N` (`PRF`, CBD, NTT); `u[i]` is
`enc4Row i`: the entries `Â[j, i]` for `j < 4`, each sampled, masked and
multiplied by `ŷ[j]` and summed (`enc4Entry`), then `NTT⁻¹`, `e₁[i]` added and
the sum compressed to 11 bits into the ciphertext; and `v` is `enc4V`: the
products of `t̂[j]` (decoded from `ek`) and `ŷ[j]` summed, `NTT⁻¹`, `e₂` and
`μ` added, and the sum compressed to 5 bits into the ciphertext.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

def e4E : Nat := 4096
def e4U : Nat := 5120
def e4A : Nat := 6144
def e4P : Nat := 7168
def e4T : Nat := 8192
def e4MU : Nat := 9216
def e4NS : Nat := 10240
def e4SS : Nat := 11264
def e4ST : Nat := 13312
def e4WK : Nat := 13512
def e4PRF : Nat := 14152
def e4ACC : Nat := 14280
def e4EK : Nat := 14284
def e4M : Nat := 15856
def e4KR : Nat := 15888
def e4C : Nat := 15956

/-- `SamplePolyCBD₂(PRF₂(r, N))` into `scratch + o`. -/
def enc4Cbd (sc N o : Nat) : Prog isa :=
  .seq (.block (st8 (e4KR + 64) N)) <|
  .seq (hash1 sc e4ST e4WK 136 0x1f ⟨sc, e4KR + 32, 33⟩ ⟨sc, e4PRF, 128⟩)
    (cbd2C sc ⟨sc, e4PRF, 128⟩ ⟨sc, o, 1024⟩)

/-- `ŷ[N] = NTT(SamplePolyCBD₂(PRF₂(r, N)))`. -/
def enc4YC (sc N : Nat) : Prog isa :=
  .seq (enc4Cbd sc N (1024 * N)) (nttC sc ⟨sc, 1024 * N, 1024⟩ ⟨sc, e4NS, 1024⟩)

/-- `Â[j, i] ← SampleNTT(ρ ‖ i ‖ j)`, masked, times `ŷ[j]`, added to `u[i]`
(written to it if `j = 0`). -/
def enc4Entry (sc i j : Nat) : Prog isa :=
  .seq (.block (st8 (e4EK + 1568) i)) <| .seq (.block (st8 (e4EK + 1569) j)) <|
  .seq (sampleC sc ⟨sc, e4EK + 1536, 34⟩ ⟨sc, e4A, 1024⟩ ⟨sc, e4SS, 2048⟩) <|
  .seq (maskA e4ACC e4A) <|
  if j = 0 then mulC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4A, 1024⟩ ⟨sc, 0, 1024⟩ ⟨sc, e4NS, 1024⟩
  else .seq (mulC sc ⟨sc, e4P, 1024⟩ ⟨sc, e4A, 1024⟩ ⟨sc, 1024 * j, 1024⟩ ⟨sc, e4NS, 1024⟩)
    (addC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4P, 1024⟩)

/-- `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, compressed into `c[352i : 352i + 352]`. -/
def enc4Row (sc i : Nat) : Prog isa :=
  .seq (enc4Entry sc i 0) <| .seq (enc4Entry sc i 1) <| .seq (enc4Entry sc i 2) <| .seq (enc4Entry sc i 3) <|
  .seq (nttInvC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4NS, 1024⟩) <| .seq (enc4Cbd sc (4 + i) e4E) <|
  .seq (addC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4E, 1024⟩) (ceC1024 sc 11 ⟨sc, e4U, 1024⟩ ⟨sc, e4C + 352 * i, 352⟩)

/-- `t̂[j] ← ByteDecode₁₂(ek[384j : 384j + 384])`, times `ŷ[j]`, added to `v`
(written to it if `j = 0`). -/
def enc4Term (sc j : Nat) : Prog isa :=
  .seq (dec12C sc ⟨sc, e4EK + 384 * j, 384⟩ ⟨sc, e4T, 1024⟩) <|
  if j = 0 then mulC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4T, 1024⟩ ⟨sc, 0, 1024⟩ ⟨sc, e4NS, 1024⟩
  else .seq (mulC sc ⟨sc, e4P, 1024⟩ ⟨sc, e4T, 1024⟩ ⟨sc, 1024 * j, 1024⟩ ⟨sc, e4NS, 1024⟩)
    (addC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4P, 1024⟩)

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + μ`, compressed into `c[1408 : 1568]`. -/
def enc4V (sc : Nat) : Prog isa :=
  .seq (enc4Term sc 0) <| .seq (enc4Term sc 1) <| .seq (enc4Term sc 2) <| .seq (enc4Term sc 3) <|
  .seq (nttInvC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4NS, 1024⟩) <| .seq (enc4Cbd sc 8 e4E) <|
  .seq (addC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4E, 1024⟩) <|
  .seq (ddC sc 1 ⟨sc, e4M, 32⟩ ⟨sc, e4MU, 1024⟩) <| .seq (addC sc ⟨sc, e4U, 1024⟩ ⟨sc, e4MU, 1024⟩)
    (ceC1024 sc 5 ⟨sc, e4U, 1024⟩ ⟨sc, e4C + 1408, 160⟩)

/-- K-PKE.Encrypt(ek, m, r), with `ek`, `m` and `r` in `scratch`, the ciphertext into it. -/
def encrypt4 (sc : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm 1), .store (at_ .esi e4ACC) .eax]) <|
  .seq (enc4YC sc 0) <| .seq (enc4YC sc 1) <| .seq (enc4YC sc 2) <| .seq (enc4YC sc 3) <|
  .seq (enc4Row sc 0) <| .seq (enc4Row sc 1) <| .seq (enc4Row sc 2) <| .seq (enc4Row sc 3) (enc4V sc)

end VG.Impl.MlKem1024.X86

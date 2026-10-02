import VerifiedGarbage.Impl.MlKem.X86.Top
import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on x86 (32-bit): the layout of a parameter set

`vg_mlkem768_*` and `vg_mlkem1024_*` are the same code for different
parameter sets (`KemLay`): FIPS 203's `k`, `d_u` and `d_v`, the offsets of the
buffers of `scratch` (its length is `scratch`), and the functions that compress
to `d_u` and `d_v` bits and decompress from them (`ceK`, `ddK`: those of
ML-KEM-768 are `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`,
which also handle 1 bit; ML-KEM-1024 has its own for 5 and 11 bits). The code
over the `k` rows, entries or polynomials is unrolled (`seqs`).

`scratch` holds, for key generation (`kg*`):

* `[0, 2048k)`: `ŝ[0]` … `ŝ[k - 1]`, `ê[0]` … `ê[k - 1]`, 1024 bytes each;
* `kgT`: `t̂[i]`, as it is summed; `kgA`: `Â[i, j]`; `kgP`: a product;
* `kgNS`: the scratch of the NTT and of the products; `kgSS`: that of
  `vg_mlkem_sample_ntt`; `kgST`, `kgWK`: the Keccak state and working space;
* `kgRS`: `ρ ‖ σ = G(d ‖ k)`, followed by a byte (`kgRS + 64`): the `k` of
  `G`'s input, then the `N` of `PRF(σ, N)`, which is `σ ‖ N` at `kgRS + 32`;
  `ρ ‖ j ‖ i`, the seed of `Â[i, j]`, then overwrites the start of `σ`;
* `kgPRF`: the output of `PRF`; `kgACC`: the AND of the values
  `vg_mlkem_sample_ntt` returned (initially 1), which keygen returns.

and for K-PKE.Encrypt (`e*`), which encapsulation and decapsulation share:

* `[0, 1024k)`: `ŷ[0]` … `ŷ[k - 1]`, 1024 bytes each;
* `eE`: `e₁[i]` or `e₂`; `eU`: `u[i]`, then `v`, as it is summed; `eA`:
  `Â[j, i]`; `eP`: a product; `eT`: `t̂[j]`; `eMU`: `μ`;
* `eNS`: the scratch of the NTT and of the products; `eSS`: that of
  `vg_mlkem_sample_ntt`; `eST`, `eWK`: the Keccak state and working space;
* `ePRF`: the output of `PRF`; `eACC`: the AND of the values
  `vg_mlkem_sample_ntt` returned (set to 1 first);
* `eEK`: `ek` (`384k + 32` bytes), then `i` and `j`, so that `ρ ‖ i ‖ j` (the
  seed of `Â[j, i]`) is at `eEK + 384k`;
* `eM`: `m`; `eKR`: 64 bytes whose last 32 are `r`, then the `N` of
  `PRF(r, N)`, so that `r ‖ N` is at `eKR + 32`;
* `eC`: the ciphertext (`32(d_u·k + d_v)` bytes);
* `eH`: `H(ek)` in encapsulation, `K̄` in decapsulation.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- A parameter set's layout of `scratch`, and its functions that compress to `d_u` and `d_v` bits. -/
structure KemLay where
  p : Spec.MlKem.Params
  scratch : Nat
  kgT : Nat
  kgA : Nat
  kgP : Nat
  kgNS : Nat
  kgSS : Nat
  kgST : Nat
  kgWK : Nat
  kgRS : Nat
  kgPRF : Nat
  kgACC : Nat
  eE : Nat
  eU : Nat
  eA : Nat
  eP : Nat
  eT : Nat
  eMU : Nat
  eNS : Nat
  eSS : Nat
  eST : Nat
  eWK : Nat
  ePRF : Nat
  eACC : Nat
  eEK : Nat
  eM : Nat
  eKR : Nat
  eC : Nat
  eH : Nat
  ceName : String
  ceCode : Prog isa
  ddName : String
  ddCode : Prog isa

/-- `c₀`, …, `cₙ₋₁`, then `c`. -/
def seqs : List (Prog isa) → Prog isa → Prog isa
  | [], c => c
  | c₀ :: cs, c => .seq c₀ (seqs cs c)

/-- `o ← ByteEncode_d(Compress_d(f))`, for `d` = `d_u` or `d_v`, as `ceC`. -/
def ceK (L : KemLay) (sc d : Nat) (f o : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo sc .edx o ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr)))
    (callWith [.edi, .edx, .ecx, .eax] L.ceName L.ceCode)

/-- `f ← Decompress_d(ByteDecode_d(b))`, for `d` = `d_u` or `d_v`, as `ddC`. -/
def ddK (L : KemLay) (sc d : Nat) (b f : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax b ++ ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))),
      .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo sc .edi f))
    (callWith [.edi, .edx, .ecx, .eax] L.ddName L.ddCode)

/-- ML-KEM-768. -/
def L768 : KemLay where
  p := Spec.MlKem.mlKem768
  scratch := 32768
  kgT := 6144
  kgA := 7168
  kgP := 8192
  kgNS := 9216
  kgSS := 10240
  kgST := 12288
  kgWK := 12488
  kgRS := 13128
  kgPRF := 13200
  kgACC := 13328
  eE := 3072
  eU := 4096
  eA := 5120
  eP := 6144
  eT := 7168
  eMU := 8192
  eNS := 9216
  eSS := 10240
  eST := 12288
  eWK := 12488
  ePRF := 13128
  eACC := 13256
  eEK := 13260
  eM := 14448
  eKR := 14480
  eC := 14548
  eH := 15640
  ceName := "vg_mlkem_compress_encode"
  ceCode := compressEncode
  ddName := "vg_mlkem_decode_decompress"
  ddCode := decodeDecompress

end VG.Impl.MlKem.X86

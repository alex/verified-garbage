import VerifiedGarbage.Impl.MlKem1024.X86.Top

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_keygen`

`keyGen(seed, ek, dk, scratch) -> eax`: `ML-KEM.KeyGen_internal(d, z)`
(Algorithm 16) with `d = seed[0 : 32]` and `z = seed[32 : 64]`, as
`vg_mlkem768_keygen` (`Impl/MlKem/X86/KeyGen.lean`) computes it for `k = 3`,
here for `k = 4`. `scratch` (argument 3, in `esi`) holds, at these offsets:

* `[0, 8192)`: `ŝ[0]` … `ŝ[3]`, `ê[0]` … `ê[3]`, 1024 bytes each;
* `kg4T`: `t̂[i]`, as it is summed; `kg4A`: `Â[i, j]`; `kg4P`: a product;
* `kg4NS`: the scratch of the NTT and of the products; `kg4SS`: that of
  `vg_mlkem_sample_ntt`; `kg4ST`, `kg4WK`: the Keccak state and working space;
* `kg4RS`: `ρ ‖ σ = G(d ‖ 4)`, followed by a byte (`kg4RS + 64`): the `4` of
  `G`'s input, then the `N` of `PRF(σ, N)`, which is `σ ‖ N` at `kg4RS + 32`;
  `ρ ‖ j ‖ i`, the seed of `Â[i, j]`, then overwrites the start of `σ`;
* `kg4PRF`: the output of `PRF`; `kg4ACC`: the AND of the values
  `vg_mlkem_sample_ntt` returned (initially 1), which keygen returns.

The code is unrolled: `ŝ` and `ê` are `kg4Prf N` for `N < 8` (`PRF`, CBD,
NTT), and `t̂[i]` is `kg4Row i`: the four entries of row `i` of `Â`, each
sampled and masked (`maskA`), multiplied by `ŝ[j]` and summed, then `ê[i]`
added and the sum encoded into `ek`. Then `ρ` is copied into `ek`, `ŝ`
encoded into `dk`, `ek` copied into `dk`, `H(ek)` hashed into `dk`, and `z`
copied into `dk`.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

def kg4T : Nat := 8192
def kg4A : Nat := 9216
def kg4P : Nat := 10240
def kg4NS : Nat := 11264
def kg4SS : Nat := 12288
def kg4ST : Nat := 14336
def kg4WK : Nat := 14536
def kg4RS : Nat := 15176
def kg4PRF : Nat := 15248
def kg4ACC : Nat := 15376

/-- `ŝ[N]` (`N < 4`) or `ê[N - 4]`: `NTT(SamplePolyCBD₂(PRF₂(σ, N)))`. -/
def kg4Prf (N : Nat) : Prog isa :=
  .seq (.block (st8 (kg4RS + 64) N)) <|
  .seq (hash1 3 kg4ST kg4WK 136 0x1f ⟨3, kg4RS + 32, 33⟩ ⟨3, kg4PRF, 128⟩) <|
  .seq (cbd2C 3 ⟨3, kg4PRF, 128⟩ ⟨3, 1024 * N, 1024⟩) (nttC 3 ⟨3, 1024 * N, 1024⟩ ⟨3, kg4NS, 1024⟩)

/-- `Â[i, j] ← SampleNTT(ρ ‖ j ‖ i)`, masked, times `ŝ[j]`, added to `t̂[i]`
(written to it if `j = 0`). -/
def kg4Entry (i j : Nat) : Prog isa :=
  .seq (.block (st8 (kg4RS + 32) j)) <| .seq (.block (st8 (kg4RS + 33) i)) <|
  .seq (sampleC 3 ⟨3, kg4RS, 34⟩ ⟨3, kg4A, 1024⟩ ⟨3, kg4SS, 2048⟩) <|
  .seq (maskA kg4ACC kg4A) <|
  if j = 0 then mulC 3 ⟨3, kg4T, 1024⟩ ⟨3, kg4A, 1024⟩ ⟨3, 0, 1024⟩ ⟨3, kg4NS, 1024⟩
  else .seq (mulC 3 ⟨3, kg4P, 1024⟩ ⟨3, kg4A, 1024⟩ ⟨3, 1024 * j, 1024⟩ ⟨3, kg4NS, 1024⟩)
    (addC 3 ⟨3, kg4T, 1024⟩ ⟨3, kg4P, 1024⟩)

/-- `t̂[i]`, encoded into `ek[384i : 384i + 384]`. -/
def kg4Row (i : Nat) : Prog isa :=
  .seq (kg4Entry i 0) <| .seq (kg4Entry i 1) <| .seq (kg4Entry i 2) <| .seq (kg4Entry i 3) <|
  .seq (addC 3 ⟨3, kg4T, 1024⟩ ⟨3, 1024 * (4 + i), 1024⟩) (enc12C 3 ⟨3, kg4T, 1024⟩ ⟨1, 384 * i, 384⟩)

def kg4Body : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
  .seq (.block [.mov .eax (.imm 1), .store (at_ .esi kg4ACC) .eax]) <|
  .seq (.block (st8 (kg4RS + 64) 4)) <|
  .seq (hash2 3 kg4ST kg4WK 72 6 ⟨0, 0, 32⟩ ⟨3, kg4RS + 64, 1⟩ ⟨3, kg4RS, 64⟩) <|
  .seq (kg4Prf 0) <| .seq (kg4Prf 1) <| .seq (kg4Prf 2) <| .seq (kg4Prf 3) <|
  .seq (kg4Prf 4) <| .seq (kg4Prf 5) <| .seq (kg4Prf 6) <| .seq (kg4Prf 7) <|
  .seq (kg4Row 0) <| .seq (kg4Row 1) <| .seq (kg4Row 2) <| .seq (kg4Row 3) <|
  .seq (copyW 3 ⟨3, kg4RS, 32⟩ ⟨1, 1536, 32⟩ 8) <|
  .seq (enc12C 3 ⟨3, 0, 1024⟩ ⟨2, 0, 384⟩) <| .seq (enc12C 3 ⟨3, 1024, 1024⟩ ⟨2, 384, 384⟩) <|
  .seq (enc12C 3 ⟨3, 2048, 1024⟩ ⟨2, 768, 384⟩) <| .seq (enc12C 3 ⟨3, 3072, 1024⟩ ⟨2, 1152, 384⟩) <|
  .seq (copyW 3 ⟨1, 0, 1568⟩ ⟨2, 1536, 1568⟩ 392) <|
  .seq (hash1 3 kg4ST kg4WK 136 6 ⟨1, 0, 1568⟩ ⟨2, 3104, 32⟩) <|
  .seq (copyW 3 ⟨0, 32, 32⟩ ⟨2, 3136, 32⟩ 8) (.block [.mov .eax (.mem (at_ .esi kg4ACC))])

def keyGen : Prog isa := leaf kg4Body

end VG.Impl.MlKem1024.X86

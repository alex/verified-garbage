import VerifiedGarbage.Impl.MlKem.X86.Top

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_keygen`

`keyGen(seed, ek, dk, scratch) -> eax`: `ML-KEM.KeyGen_internal(d, z)`
(Algorithm 16) with `d = seed[0 : 32]` and `z = seed[32 : 64]`, as calls of
the primitives and the Keccak functions (`Top.lean`). `scratch` (argument 3,
in `esi`) holds, at these offsets:

* `[0, 6144)`: `ŝ[0]`, `ŝ[1]`, `ŝ[2]`, `ê[0]`, `ê[1]`, `ê[2]`, 1024 bytes each;
* `kgT`: `t̂[i]`, as it is summed; `kgA`: `Â[i, j]`; `kgP`: a product;
* `kgNS`: the scratch of the NTT and of the products; `kgSS`: that of
  `vg_mlkem_sample_ntt`; `kgST`, `kgWK`: the Keccak state and working space;
* `kgRS`: `ρ ‖ σ = G(d ‖ 3)`, followed by a byte (`kgRS + 64`): the `3` of
  `G`'s input, then the `N` of `PRF(σ, N)`, which is `σ ‖ N` at `kgRS + 32`;
  `ρ ‖ j ‖ i`, the seed of `Â[i, j]`, then overwrites the start of `σ`;
* `kgPRF`: the output of `PRF`; `kgACC`: the AND of the values
  `vg_mlkem_sample_ntt` returned (initially 1), which keygen returns.

The code is unrolled: `ŝ` and `ê` are `kgPrf N` for `N < 6` (`PRF`, CBD, NTT),
and `t̂[i]` is `kgRow i`: the three entries of row `i` of `Â`, each sampled
and masked (`maskA`), multiplied by `ŝ[j]` and summed, then `ê[i]` added and
the sum encoded into `ek`. Then `ρ` is copied into `ek`, `ŝ` encoded into
`dk`, `ek` copied into `dk`, `H(ek)` hashed into `dk`, and `z` copied into
`dk`.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

def kgT : Nat := 6144
def kgA : Nat := 7168
def kgP : Nat := 8192
def kgNS : Nat := 9216
def kgSS : Nat := 10240
def kgST : Nat := 12288
def kgWK : Nat := 12488
def kgRS : Nat := 13128
def kgPRF : Nat := 13200
def kgACC : Nat := 13328

/-- `ŝ[N]` (`N < 3`) or `ê[N - 3]`: `NTT(SamplePolyCBD₂(PRF₂(σ, N)))`. -/
def kgPrf (N : Nat) : Prog isa :=
  .seq (.block (st8 (kgRS + 64) N)) <|
  .seq (hash1 3 kgST kgWK 136 0x1f ⟨3, kgRS + 32, 33⟩ ⟨3, kgPRF, 128⟩) <|
  .seq (cbd2C 3 ⟨3, kgPRF, 128⟩ ⟨3, 1024 * N, 1024⟩) (nttC 3 ⟨3, 1024 * N, 1024⟩ ⟨3, kgNS, 1024⟩)

/-- `Â[i, j] ← SampleNTT(ρ ‖ j ‖ i)`, masked, times `ŝ[j]`, added to `t̂[i]`
(written to it if `j = 0`). -/
def kgEntry (i j : Nat) : Prog isa :=
  .seq (.block (st8 (kgRS + 32) j)) <| .seq (.block (st8 (kgRS + 33) i)) <|
  .seq (sampleC 3 ⟨3, kgRS, 34⟩ ⟨3, kgA, 1024⟩ ⟨3, kgSS, 2048⟩) <|
  .seq (maskA kgACC kgA) <|
  if j = 0 then mulC 3 ⟨3, kgT, 1024⟩ ⟨3, kgA, 1024⟩ ⟨3, 0, 1024⟩ ⟨3, kgNS, 1024⟩
  else .seq (mulC 3 ⟨3, kgP, 1024⟩ ⟨3, kgA, 1024⟩ ⟨3, 1024 * j, 1024⟩ ⟨3, kgNS, 1024⟩)
    (addC 3 ⟨3, kgT, 1024⟩ ⟨3, kgP, 1024⟩)

/-- `t̂[i]`, encoded into `ek[384i : 384i + 384]`. -/
def kgRow (i : Nat) : Prog isa :=
  .seq (kgEntry i 0) <| .seq (kgEntry i 1) <| .seq (kgEntry i 2) <|
  .seq (addC 3 ⟨3, kgT, 1024⟩ ⟨3, 1024 * (3 + i), 1024⟩) (enc12C 3 ⟨3, kgT, 1024⟩ ⟨1, 384 * i, 384⟩)

def kgBody : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
  .seq (.block [.mov .eax (.imm 1), .store (at_ .esi kgACC) .eax]) <|
  .seq (.block (st8 (kgRS + 64) 3)) <|
  .seq (hash2 3 kgST kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, kgRS + 64, 1⟩ ⟨3, kgRS, 64⟩) <|
  .seq (kgPrf 0) <| .seq (kgPrf 1) <| .seq (kgPrf 2) <| .seq (kgPrf 3) <| .seq (kgPrf 4) <| .seq (kgPrf 5) <|
  .seq (kgRow 0) <| .seq (kgRow 1) <| .seq (kgRow 2) <|
  .seq (copyW 3 ⟨3, kgRS, 32⟩ ⟨1, 1152, 32⟩ 8) <|
  .seq (enc12C 3 ⟨3, 0, 1024⟩ ⟨2, 0, 384⟩) <| .seq (enc12C 3 ⟨3, 1024, 1024⟩ ⟨2, 384, 384⟩) <|
  .seq (enc12C 3 ⟨3, 2048, 1024⟩ ⟨2, 768, 384⟩) <|
  .seq (copyW 3 ⟨1, 0, 1184⟩ ⟨2, 1152, 1184⟩ 296) <|
  .seq (hash1 3 kgST kgWK 136 6 ⟨1, 0, 1184⟩ ⟨2, 2336, 32⟩) <|
  .seq (copyW 3 ⟨0, 32, 32⟩ ⟨2, 2368, 32⟩ 8) (.block [.mov .eax (.mem (at_ .esi kgACC))])

def keyGen : Prog isa := leaf kgBody

end VG.Impl.MlKem.X86

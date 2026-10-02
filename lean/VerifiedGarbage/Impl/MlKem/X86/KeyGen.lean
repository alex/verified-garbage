import VerifiedGarbage.Impl.MlKem.X86.Kem

/-!
# ML-KEM on x86 (32-bit): key generation

`keyGen(seed, ek, dk, scratch) -> eax`: `ML-KEM.KeyGen_internal(d, z)`
(Algorithm 16) with `d = seed[0 : 32]` and `z = seed[32 : 64]`, as calls of
the primitives and the Keccak functions (`Top.lean`), with `scratch`
(argument 3, in `esi`) laid out as `L` says (`Kem.lean`).

The code is unrolled: `ŝ` and `ê` are `kgPrf L N` for `N < 2k` (`PRF`, CBD,
NTT), and `t̂[i]` is `kgRow L i`: the `k` entries of row `i` of `Â`, each
sampled and masked (`maskA`), multiplied by `ŝ[j]` and summed, then `ê[i]`
added and the sum encoded into `ek`. Then `ρ` is copied into `ek`, `ŝ` encoded
into `dk`, `ek` copied into `dk`, `H(ek)` hashed into `dk`, and `z` copied into
`dk`. `vg_mlkem768_keygen` is `keyGen` (`L768`).
-/

namespace VG.Impl.MlKem.X86

open VG.X86

variable (L : KemLay)

/-- `ŝ[N]` (`N < k`) or `ê[N - k]`: `NTT(SamplePolyCBD₂(PRF₂(σ, N)))`. -/
def kgPrf (N : Nat) : Prog isa :=
  .seq (.block (st8 (L.kgRS + 64) N)) <|
  .seq (hash1 3 L.kgST L.kgWK 136 0x1f ⟨3, L.kgRS + 32, 33⟩ ⟨3, L.kgPRF, 128⟩) <|
  .seq (cbd2C 3 ⟨3, L.kgPRF, 128⟩ ⟨3, 1024 * N, 1024⟩) (nttC 3 ⟨3, 1024 * N, 1024⟩ ⟨3, L.kgNS, 1024⟩)

/-- `Â[i, j] ← SampleNTT(ρ ‖ j ‖ i)`, masked, times `ŝ[j]`, added to `t̂[i]`
(written to it if `j = 0`). -/
def kgEntry (i j : Nat) : Prog isa :=
  .seq (.block (st8 (L.kgRS + 32) j)) <| .seq (.block (st8 (L.kgRS + 33) i)) <|
  .seq (sampleC 3 ⟨3, L.kgRS, 34⟩ ⟨3, L.kgA, 1024⟩ ⟨3, L.kgSS, 2048⟩) <|
  .seq (maskA L.kgACC L.kgA) <|
  if j = 0 then mulC 3 ⟨3, L.kgT, 1024⟩ ⟨3, L.kgA, 1024⟩ ⟨3, 0, 1024⟩ ⟨3, L.kgNS, 1024⟩
  else .seq (mulC 3 ⟨3, L.kgP, 1024⟩ ⟨3, L.kgA, 1024⟩ ⟨3, 1024 * j, 1024⟩ ⟨3, L.kgNS, 1024⟩)
    (addC 3 ⟨3, L.kgT, 1024⟩ ⟨3, L.kgP, 1024⟩)

/-- `t̂[i]`, encoded into `ek[384i : 384i + 384]`. -/
def kgRow (i : Nat) : Prog isa :=
  seqs ((List.range L.p.k).map (kgEntry L i)) <|
  .seq (addC 3 ⟨3, L.kgT, 1024⟩ ⟨3, 1024 * (L.p.k + i), 1024⟩) (enc12C 3 ⟨3, L.kgT, 1024⟩ ⟨1, 384 * i, 384⟩)

/-- `dk[384j : 384j + 384] ← ByteEncode₁₂(ŝ[j])`. -/
def kgEnc (j : Nat) : Prog isa := enc12C 3 ⟨3, 1024 * j, 1024⟩ ⟨2, 384 * j, 384⟩

def kgBody : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
  .seq (.block [.mov .eax (.imm 1), .store (at_ .esi L.kgACC) .eax]) <|
  .seq (.block (st8 (L.kgRS + 64) L.p.k)) <|
  .seq (hash2 3 L.kgST L.kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgRS, 64⟩) <|
  seqs ((List.range (2 * L.p.k)).map (kgPrf L)) <|
  seqs ((List.range L.p.k).map (kgRow L)) <|
  .seq (copyW 3 ⟨3, L.kgRS, 32⟩ ⟨1, 384 * L.p.k, 32⟩ 8) <|
  seqs ((List.range L.p.k).map kgEnc) <|
  .seq (copyW 3 ⟨1, 0, L.p.ekLen⟩ ⟨2, 384 * L.p.k, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
  .seq (hash1 3 L.kgST L.kgWK 136 6 ⟨1, 0, L.p.ekLen⟩ ⟨2, 768 * L.p.k + 32, 32⟩) <|
  .seq (copyW 3 ⟨0, 32, 32⟩ ⟨2, 768 * L.p.k + 64, 32⟩ 8) (.block [.mov .eax (.mem (at_ .esi L.kgACC))])

/-- `vg_mlkem768_keygen`. -/
def keyGen : Prog isa := leaf (kgBody L768)

end VG.Impl.MlKem.X86

import VerifiedGarbage.Impl.MlKem.AArch64.Lay

/-!
# ML-KEM on AArch64: `vg_mlkem768_keygen` and `vg_mlkem1024_keygen`

`(L.keyGenWith c)(seed = x0, ek = x1, dk = x2, scratch = x3) -> x0`:
`KeyGen_internal(d, z)` (FIPS 203 Algorithms 16 and 13) of the parameter set
`L` (`KemLay`) with `d ‖ z` at `seed`, as calls of the
verified primitives and Keccak functions. We keep `seed`, `ek`, `dk` and
`scratch` in `x25`–`x28` and the AND of `sample_ntt`'s results in `x24`
(callee-saved, so the callees keep them), and save our caller's values of
them and of `x30` in `scratch`.

1. `(ρ, σ) = G(d ‖ k)`, into `ρ ‖ j ‖ i` (the seed of `Â[i, j]`) and
   `σ ‖ N` (the input of `PRF(σ, N)`) in `scratch`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the `k²` entries `(i, j)`.
3. `ŝ[j] = NTT(SamplePolyCBD₂(PRF₂(σ, j)))`, and `ByteEncode₁₂(ŝ[j])` into
   `dk`; then `ê[i]` likewise from `PRF₂(σ, k + i)`, and
   `t̂[i] = Â[i, 0] ŝ[0] + ⋯ + Â[i, k - 1] ŝ[k - 1] + ê[i]`, and
   `ByteEncode₁₂(t̂[i])` into `ek` and into `dk`'s copy of `ek`.
4. `ρ` into `ek` and `dk`, `H(ek)` into `dk`, and `z` into `dk`.

Returns 1 if every `SampleNTT` finished within 280 iterations, and 0 if not
(when `ek` and `dk` are then unspecified).

`scratch` holds, at these offsets: the Keccak state (0) and working space
(200), `ρ ‖ j ‖ i` (840), `σ ‖ N` (880), the byte `k` (920), `PRF`'s output
(928), `sample_ntt`'s working space (1056), the NTT's (3104), `Â` (4128, row
by row), and after it `ŝ`, `ê[i]`, `t̂[i]`, a product and the saved
registers (`KG`; for ML-KEM-768 at 13344, 16416, 17440, 18464 and 19488).

Only the calls of `sample_ntt` depend on `ρ` (which the contract declares
that the function may leak); every other address and branch depends only on
the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

namespace KG

def ST : Nat := 0
def WK : Nat := 200
def SB : Nat := 840
def SG : Nat := 880
def BK : Nat := 920
def PB : Nat := 928
def SS : Nat := 1056
def NS : Nat := 3104
def AH : Nat := 4128

variable (L : KemLay)

def SH : Nat := AH + 1024 * (L.k * L.k)
def EP : Nat := SH L + 1024 * L.k
def TP : Nat := EP L + 1024
def PP : Nat := TP L + 1024
def SV : Nat := PP L + 1024

/-- `Â[i, j]`. -/
def aOff (i j : Nat) : Nat := AH + 1024 * (L.k * i + j)
/-- `ŝ[j]`. -/
def sOff (j : Nat) : Nat := SH L + 1024 * j

end KG

open KG

/-- Copy the 32 bytes at `sb + so` to `db + do`. -/
def copy32 (sb : Reg) (so : Nat) (db : Reg) (dO : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [.ldr .x .x9 sb (so + 8 * k), .str .x .x9 db (dO + 8 * k)]

/-- `SampleNTT`, and its result ANDed into `x24`. -/
def kgCallWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.call ("vg_mlkem_sample_ntt" ++ c.suffix) (sampleNTTWith c)) (.block [.logic .and .x .x24 .x24 .x0])

/-- `ByteEncode₁₂` of the polynomial at `off` into `b + o`. -/
def kgEnc (off : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 b o)) (.call "vg_mlkem_encode12" encode12)

/-- `h ← f ×_T g` (with `x3` the NTT's working space). -/
def kgMul (h f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 h ++ ptrTo .x1 .x28 f ++ ptrTo .x2 .x28 g ++ ptrTo .x3 .x28 NS))
    (.call "vg_mlkem_multiply_ntts" multiplyNTTs)

namespace KemLay

variable (L : KemLay)

/-- Save our caller's registers, keep the pointers, and store the byte `k`. -/
def kgPrologue : List Instr :=
  [.str .x .x24 .x3 (SV L), .str .x .x25 .x3 (SV L + 8), .str .x .x26 .x3 (SV L + 16),
    .str .x .x27 .x3 (SV L + 24), .str .x .x28 .x3 (SV L + 32), .str .x .x30 .x3 (SV L + 40), mov .x25 .x0,
    mov .x26 .x1, mov .x27 .x2, mov .x28 .x3, .movz .x .x24 1 0, .movz .x .x9 (BitVec.ofNat 16 L.k) 0,
    .strb .x9 .x28 BK]

/-- `(ρ, σ) = G(d ‖ k)`. -/
def kgGWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  hashWith c .x28 ST WK 72 6 [⟨.x25, 0, 32⟩, ⟨.x28, BK, 1⟩] [⟨.x28, SB, 32⟩, ⟨.x28, SG, 32⟩]

def kgAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := .seq (.block L.kgPrologue) (kgGWith c)

/-- The seed `ρ ‖ j ‖ i` and the arguments of `SampleNTT` for `Â[i, j]`. -/
def kgSetup (i j : Nat) : List Instr :=
  [.movz .x .x9 (BitVec.ofNat 16 j) 0, .strb .x9 .x28 (SB + 32), .movz .x .x9 (BitVec.ofNat 16 i) 0,
    .strb .x9 .x28 (SB + 33)] ++ ptrTo .x0 .x28 SB ++ ptrTo .x1 .x28 (aOff L i j) ++ ptrTo .x2 .x28 SS

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`, and its result ANDed into `x24`. -/
def kgSampleWith (c : Impl.Sha3.AArch64.Callee) (i j : Nat) : Prog isa :=
  .seq (.block (L.kgSetup i j)) (kgCallWith c)

/-- The `k²` `SampleNTT`s, row by row. -/
def kgBWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  seqs ((List.range L.k).flatMap fun i => (List.range L.k).map fun j => L.kgSampleWith c i j)

/-- `SamplePolyCBD₂(PRF₂(σ, N))` into the polynomial at `off`, then its NTT. -/
def kgCbdNttWith (c : Impl.Sha3.AArch64.Callee) (N off : Nat) : Prog isa :=
  .seq (.block [.movz .x .x9 (BitVec.ofNat 16 N) 0, .strb .x9 .x28 (SG + 32)]) <|
  .seq (hashWith c .x28 ST WK 136 0x1f [⟨.x28, SG, 33⟩] [⟨.x28, PB, 128⟩]) <|
  .seq (.seq (.block (ptrTo .x0 .x28 PB ++ ptrTo .x1 .x28 off)) (.call "vg_mlkem_cbd2" cbd2))
    (.seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 NS)) (.call "vg_mlkem_ntt" ntt))

/-- `ŝ[j]`, and its encoding into `dk`. -/
def kgSWith (c : Impl.Sha3.AArch64.Callee) (j : Nat) : Prog isa :=
  .seq (kgCbdNttWith c j (sOff L j)) (kgEnc (sOff L j) .x27 (384 * j))

/-- `ê[i]` and `t̂[i]`, and the encoding of `t̂[i]` into `ek` and `dk`. -/
def kgTWith (c : Impl.Sha3.AArch64.Callee) (i : Nat) : Prog isa :=
  seqs (kgCbdNttWith c (L.k + i) (EP L) ::
    dotSteps (TP L) (PP L) (fun j h => [kgMul h (aOff L i j) (sOff L j)]) L.k ++
    [addAt (TP L) (EP L), kgEnc (TP L) .x26 (384 * i), kgEnc (TP L) .x27 (384 * L.k + 384 * i)])

/-- `ρ` into `ek` and `dk`, `H(ek)`, `z`, the result, and our caller's registers back. -/
def kgEndWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (copy32 .x28 SB .x26 (384 * L.k) ++ copy32 .x28 SB .x27 (768 * L.k))) <|
  .seq (hashWith c .x28 ST WK 136 6 [⟨.x26, 0, L.ekLen⟩] [⟨.x27, 768 * L.k + 32, 32⟩]) <|
  .block (copy32 .x25 32 .x27 (768 * L.k + 64) ++
    ([mov .x0 .x24, .ldr .x .x30 .x28 (SV L + 40), .ldr .x .x24 .x28 (SV L), .ldr .x .x25 .x28 (SV L + 8),
      .ldr .x .x26 .x28 (SV L + 16), .ldr .x .x27 .x28 (SV L + 24), .ldr .x .x28 .x28 (SV L + 32)] :
      List Instr))

def kgCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  seqs ((List.range L.k).map (L.kgSWith c) ++ (List.range L.k).map (L.kgTWith c) ++ [L.kgEndWith c])

def keyGenWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (L.kgAWith c) (.seq (L.kgBWith c) (L.kgCWith c))

end KemLay

abbrev kgAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay768.kgAWith c
abbrev kgCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay768.kgCWith c
abbrev keyGenWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay768.keyGenWith c
abbrev keyGen : Prog isa := keyGenWith .scalar

end VG.Impl.MlKem.AArch64

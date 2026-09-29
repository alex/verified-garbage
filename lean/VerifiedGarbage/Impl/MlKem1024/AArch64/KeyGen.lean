import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`

`keyGen(seed = x0, ek = x1, dk = x2, scratch = x3) -> x0`: `KeyGen_internal(d, z)`
(FIPS 203 Algorithms 16 and 13) of ML-KEM-1024 with `d ‖ z` at `seed`, as
calls of the verified primitives and Keccak functions, as ML-KEM-768's
(`Impl/MlKem/AArch64/KeyGen.lean`) for `k = 4`. We keep `seed`, `ek`, `dk`
and `scratch` in `x25`–`x28` and the AND of `sample_ntt`'s results in `x24`
(callee-saved, so the callees keep them), and save our caller's values of
them and of `x30` in `scratch`.

1. `(ρ, σ) = G(d ‖ 4)`, into `ρ ‖ j ‖ i` (the seed of `Â[i, j]`) and
   `σ ‖ N` (the input of `PRF(σ, N)`) in `scratch`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the sixteen `(i, j)`.
3. `ŝ[j] = NTT(SamplePolyCBD₂(PRF₂(σ, j)))`, and `ByteEncode₁₂(ŝ[j])` into
   `dk`; then `ê[i]` likewise from `PRF₂(σ, 4 + i)`, and
   `t̂[i] = Â[i, 0] ŝ[0] + Â[i, 1] ŝ[1] + Â[i, 2] ŝ[2] + Â[i, 3] ŝ[3] + ê[i]`,
   and `ByteEncode₁₂(t̂[i])` into `ek` and into `dk`'s copy of `ek`.
4. `ρ` into `ek` and `dk`, `H(ek)` into `dk`, and `z` into `dk`.

Returns 1 if every `SampleNTT` finished within 280 iterations, and 0 if not
(when `ek` and `dk` are then unspecified).

`scratch` (48 KiB) holds, at these offsets: the Keccak state (0) and working
space (200), `ρ ‖ j ‖ i` (840), `σ ‖ N` (880), the byte 4 (920), `PRF`'s
output (928), `sample_ntt`'s working space (1056), the NTT's (3104), `Â`
(4128, row by row), `ŝ` (20512), `ê[i]` (24608), `t̂[i]` (25632), a product
(26656), and the saved registers (27680).

Only the calls of `sample_ntt` depend on `ρ` (which the contract declares
that the function may leak); every other address and branch depends only on
the pointers.
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash copy32 sampleNTT cbd2 ntt encode12 multiplyNTTs add)

namespace KG

def ST : Nat := 0
def WK : Nat := 200
def SB : Nat := 840
def SG : Nat := 880
def B4 : Nat := 920
def PB : Nat := 928
def SS : Nat := 1056
def NS : Nat := 3104
def AH : Nat := 4128
def SH : Nat := 20512
def EP : Nat := 24608
def TP : Nat := 25632
def PP : Nat := 26656
def SV : Nat := 27680

/-- `Â[i, j]`. -/
def aOff (i j : Nat) : Nat := AH + 1024 * (4 * i + j)
/-- `ŝ[j]`. -/
def sOff (j : Nat) : Nat := SH + 1024 * j

end KG

open KG

/-- Save our caller's registers, keep the pointers, and store the byte 4. -/
def kgPrologue : List Instr :=
  [.str .x .x24 .x3 SV, .str .x .x25 .x3 (SV + 8), .str .x .x26 .x3 (SV + 16), .str .x .x27 .x3 (SV + 24),
    .str .x .x28 .x3 (SV + 32), .str .x .x30 .x3 (SV + 40), mov .x25 .x0, mov .x26 .x1, mov .x27 .x2,
    mov .x28 .x3, .movz .x .x24 1 0, .movz .x .x9 4 0, .strb .x9 .x28 B4]

/-- `(ρ, σ) = G(d ‖ 4)`. -/
def kgG : Prog isa :=
  hash .x28 ST WK 72 6 [⟨.x25, 0, 32⟩, ⟨.x28, B4, 1⟩] [⟨.x28, SB, 32⟩, ⟨.x28, SG, 32⟩]

def kgA : Prog isa := .seq (.block kgPrologue) kgG

/-- The seed `ρ ‖ j ‖ i` and the arguments of `SampleNTT` for `Â[i, j]`. -/
def kgSetup (i j : Nat) : List Instr :=
  [.movz .x .x9 (BitVec.ofNat 16 j) 0, .strb .x9 .x28 (SB + 32), .movz .x .x9 (BitVec.ofNat 16 i) 0,
    .strb .x9 .x28 (SB + 33)] ++ ptrTo .x0 .x28 SB ++ ptrTo .x1 .x28 (aOff i j) ++ ptrTo .x2 .x28 SS

/-- `SampleNTT`, and its result ANDed into `x24`. -/
def kgCall : Prog isa :=
  .seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.logic .and .x .x24 .x24 .x0])

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`, and its result ANDed into `x24`. -/
def kgSample (i j : Nat) : Prog isa := .seq (.block (kgSetup i j)) kgCall

/-- The sixteen `SampleNTT`s, row by row. -/
def kgB : Prog isa :=
  .seq (kgSample 0 0) <| .seq (kgSample 0 1) <| .seq (kgSample 0 2) <| .seq (kgSample 0 3) <|
  .seq (kgSample 1 0) <| .seq (kgSample 1 1) <| .seq (kgSample 1 2) <| .seq (kgSample 1 3) <|
  .seq (kgSample 2 0) <| .seq (kgSample 2 1) <| .seq (kgSample 2 2) <| .seq (kgSample 2 3) <|
  .seq (kgSample 3 0) <| .seq (kgSample 3 1) <| .seq (kgSample 3 2) (kgSample 3 3)

/-- `SamplePolyCBD₂(PRF₂(σ, N))` into the polynomial at `off`, then its NTT. -/
def kgCbdNtt (N off : Nat) : Prog isa :=
  .seq (.block [.movz .x .x9 (BitVec.ofNat 16 N) 0, .strb .x9 .x28 (SG + 32)]) <|
  .seq (hash .x28 ST WK 136 0x1f [⟨.x28, SG, 33⟩] [⟨.x28, PB, 128⟩]) <|
  .seq (.seq (.block (ptrTo .x0 .x28 PB ++ ptrTo .x1 .x28 off)) (.call "vg_mlkem_cbd2" cbd2))
    (.seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 NS)) (.call "vg_mlkem_ntt" ntt))

/-- `ByteEncode₁₂` of the polynomial at `off` into `b + o`. -/
def kgEnc (off : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 b o)) (.call "vg_mlkem_encode12" encode12)

/-- `ŝ[j]`, and its encoding into `dk`. -/
def kgS (j : Nat) : Prog isa := .seq (kgCbdNtt j (sOff j)) (kgEnc (sOff j) .x27 (384 * j))

/-- `h ← f ×_T g` (with `x3` the NTT's working space). -/
def kgMul (h f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 h ++ ptrTo .x1 .x28 f ++ ptrTo .x2 .x28 g ++ ptrTo .x3 .x28 NS))
    (.call "vg_mlkem_multiply_ntts" multiplyNTTs)

/-- `f ← f + g`. -/
def kgAdd (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call "vg_mlkem_add" add)

/-- `ê[i]` and `t̂[i]`, and the encoding of `t̂[i]` into `ek` and `dk`. -/
def kgT (i : Nat) : Prog isa :=
  .seq (kgCbdNtt (4 + i) EP) <|
  .seq (kgMul TP (aOff i 0) (sOff 0)) <| .seq (kgMul PP (aOff i 1) (sOff 1)) <| .seq (kgAdd TP PP) <|
  .seq (kgMul PP (aOff i 2) (sOff 2)) <| .seq (kgAdd TP PP) <|
  .seq (kgMul PP (aOff i 3) (sOff 3)) <| .seq (kgAdd TP PP) <| .seq (kgAdd TP EP) <|
  .seq (kgEnc TP .x26 (384 * i)) (kgEnc TP .x27 (1536 + 384 * i))

/-- `ρ` into `ek` and `dk`, `H(ek)`, `z`, the result, and our caller's registers back. -/
def kgEnd : Prog isa :=
  .seq (.block (copy32 .x28 SB .x26 1536 ++ copy32 .x28 SB .x27 3072)) <|
  .seq (hash .x28 ST WK 136 6 [⟨.x26, 0, 1568⟩] [⟨.x27, 3104, 32⟩]) <|
  .block (copy32 .x25 32 .x27 3136 ++
    ([mov .x0 .x24, .ldr .x .x30 .x28 (SV + 40), .ldr .x .x24 .x28 SV, .ldr .x .x25 .x28 (SV + 8),
      .ldr .x .x26 .x28 (SV + 16), .ldr .x .x27 .x28 (SV + 24), .ldr .x .x28 .x28 (SV + 32)] : List Instr))

def kgC : Prog isa :=
  .seq (kgS 0) <| .seq (kgS 1) <| .seq (kgS 2) <| .seq (kgS 3) <|
  .seq (kgT 0) <| .seq (kgT 1) <| .seq (kgT 2) <| .seq (kgT 3) kgEnd

def keyGen : Prog isa := .seq kgA (.seq kgB kgC)

end VG.Impl.MlKem1024.AArch64

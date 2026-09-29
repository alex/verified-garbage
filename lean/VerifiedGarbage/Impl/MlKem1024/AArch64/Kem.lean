import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Impl.MlKem.AArch64.Kem

/-!
# ML-KEM-1024 on AArch64: what `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps` share

As ML-KEM-768's (`Impl/MlKem/AArch64/Kem.lean`), for `k = 4`, `d_u = 11` and
`d_v = 5`. Both keep four pointers in `x25`–`x28` (`scratch` in `x28`), the
AND of `sample_ntt`'s results in `x24`, and save our caller's values of
these and of `x30` in `scratch` (`kemPrologue`, `kemEpilogue`). Both run
K-PKE.Encrypt (FIPS 203 Algorithm 14) after sampling `Â` (`kemMatrix`, from
`ρ ‖ j ‖ i` at `SB`): `ŷ`, `u` and `v` (`encryptC`), with `r` at `RB`, and
`ek`, `m` and the ciphertext wherever the caller says.

`scratch` (48 KiB) holds, at these offsets: the Keccak state (0) and working
space (200), `ρ ‖ j ‖ i` (840), `H(ek)` (880), `m'` (912), `r ‖ N` (944),
`K'` (984), `K̄` (1016), `PRF`'s output (1048), `sample_ntt`'s working space
(1176), the NTT's (3224), `Â` (4248, row by row), `ŷ` (20632), a noise
polynomial (24728), a sum of products (25752), a product (26776), `t̂[j]`
(27800), `c'` (28824), and the saved registers (30392).
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash copy32 slotReg argReg kemOwn cbd2 ntt nttInv
  multiplyNTTs add sub decode12)

namespace KEM

def ST : Nat := 0
def WK : Nat := 200
def SB : Nat := 840
def HB : Nat := 880
def MB : Nat := 912
def RB : Nat := 944
def KP : Nat := 984
def JB : Nat := 1016
def PB : Nat := 1048
def SS : Nat := 1176
def NS : Nat := 3224
def AH : Nat := 4248
def YH : Nat := 20632
def EP : Nat := 24728
def TP : Nat := 25752
def PP : Nat := 26776
def TH : Nat := 27800
def CB : Nat := 28824
def SV : Nat := 30392

/-- `Â[i, j]`. -/
def aOff (i j : Nat) : Nat := AH + 1024 * (4 * i + j)
/-- `ŷ[j]`. -/
def yOff (j : Nat) : Nat := YH + 1024 * j

end KEM

open KEM

/-! ## Registers -/

/-- Save our caller's registers in `scratch` (argument `sc`), keep the
arguments `slots` in `x25`–`x28`, and set `x24` to 1. -/
def kemPrologue (sc : Nat) (slots : List Nat) : List Instr :=
  (List.range 6).map (fun k => .str .x (kemOwn.getD k .x0) (argReg sc) (SV + 8 * k)) ++
    (List.range 4).map (fun k => mov (slotReg k) (argReg (slots.getD k 0))) ++ [.movz .x .x24 1 0]

/-- The result (`x24`) in `x0`, and our caller's registers back (`x28` last). -/
def kemEpilogue : List Instr :=
  mov .x0 .x24 :: (List.range 6).map fun k => .ldr .x (kemOwn.getD k .x0) .x28 (SV + 8 * k)

/-! ## Building blocks -/

/-- `SamplePolyCBD₂(PRF₂(r, N))` into the polynomial at `off`, with `r` at `RB`. -/
def prfCbd (N off : Nat) : Prog isa :=
  .seq (.block [.movz .x .x9 (BitVec.ofNat 16 N) 0, .strb .x9 .x28 (RB + 32)]) <|
  .seq (hash .x28 ST WK 136 0x1f [⟨.x28, RB, 33⟩] [⟨.x28, PB, 128⟩]) <|
    .seq (.block (ptrTo .x0 .x28 PB ++ ptrTo .x1 .x28 off)) (.call "vg_mlkem_cbd2" cbd2)

/-- The NTT of the polynomial at `off`. -/
def nttAt (off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 NS)) (.call "vg_mlkem_ntt" ntt)

/-- The inverse NTT of the polynomial at `off`. -/
def nttInvAt (off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 NS)) (.call "vg_mlkem_inv_ntt" nttInv)

/-- `h ← f ×_T g`. -/
def mulAt (h f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 h ++ ptrTo .x1 .x28 f ++ ptrTo .x2 .x28 g ++ ptrTo .x3 .x28 NS))
    (.call "vg_mlkem_multiply_ntts" multiplyNTTs)

/-- `f ← f + g`. -/
def addAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call "vg_mlkem_add" add)

/-- `f ← f - g`. -/
def subAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call "vg_mlkem_sub" sub)

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `off` into `b + o`, for
the widths of ML-KEM-768 (here `d = 1`). -/
def ceAt (off d : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ (.movz .x .x1 (BitVec.ofNat 16 d) 0 :: ptrTo .x2 b o) ++
      ([.movz .x .x3 (BitVec.ofNat 16 (32 * d)) 0] : List Instr)))
    (.call "vg_mlkem_compress_encode" Impl.MlKem.AArch64.compressEncode)

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `off` into `b + o`, for
the widths of ML-KEM-1024 (`d` = 5 and 11). -/
def ceWAt (off d : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ (.movz .x .x1 (BitVec.ofNat 16 d) 0 :: ptrTo .x2 b o) ++
      ([.movz .x .x3 (BitVec.ofNat 16 (32 * d)) 0] : List Instr)))
    (.call "vg_mlkem1024_compress_encode" compressEncode)

/-- `Decompress_d(ByteDecode_d(b + o))` into the polynomial at `off`, for the
widths of ML-KEM-768 (here `d = 1`). -/
def ddAt (b : Reg) (o d off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ([.movz .x .x1 (BitVec.ofNat 16 (32 * d)) 0,
      .movz .x .x2 (BitVec.ofNat 16 d) 0] : List Instr) ++ ptrTo .x3 .x28 off))
    (.call "vg_mlkem_decode_decompress" Impl.MlKem.AArch64.decodeDecompress)

/-- `Decompress_d(ByteDecode_d(b + o))` into the polynomial at `off`, for the
widths of ML-KEM-1024 (`d` = 5 and 11). -/
def ddWAt (b : Reg) (o d off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ([.movz .x .x1 (BitVec.ofNat 16 (32 * d)) 0,
      .movz .x .x2 (BitVec.ofNat 16 d) 0] : List Instr) ++ ptrTo .x3 .x28 off))
    (.call "vg_mlkem1024_decode_decompress" decodeDecompress)

/-- `ByteDecode₁₂(b + o)` into the polynomial at `off`. -/
def dec12At (b : Reg) (o off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ptrTo .x1 .x28 off)) (.call "vg_mlkem_decode12" decode12)

/-! ## The matrix -/

/-- The seed `ρ ‖ j ‖ i` and the arguments of `SampleNTT` for `Â[i, j]`. -/
def kemSetup (i j : Nat) : List Instr :=
  [.movz .x .x9 (BitVec.ofNat 16 j) 0, .strb .x9 .x28 (SB + 32), .movz .x .x9 (BitVec.ofNat 16 i) 0,
    .strb .x9 .x28 (SB + 33)] ++ ptrTo .x0 .x28 SB ++ ptrTo .x1 .x28 (aOff i j) ++ ptrTo .x2 .x28 SS

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`, and its result ANDed into `x24`. -/
def kemSample (i j : Nat) : Prog isa := .seq (.block (kemSetup i j)) kgCall

/-- The sixteen `SampleNTT`s, row by row. -/
def kemMatrix : Prog isa :=
  .seq (kemSample 0 0) <| .seq (kemSample 0 1) <| .seq (kemSample 0 2) <| .seq (kemSample 0 3) <|
  .seq (kemSample 1 0) <| .seq (kemSample 1 1) <| .seq (kemSample 1 2) <| .seq (kemSample 1 3) <|
  .seq (kemSample 2 0) <| .seq (kemSample 2 1) <| .seq (kemSample 2 2) <| .seq (kemSample 2 3) <|
  .seq (kemSample 3 0) <| .seq (kemSample 3 1) <| .seq (kemSample 3 2) (kemSample 3 3)

/-! ## K-PKE.Encrypt after the matrix -/

/-- `ŷ[j] = NTT(SamplePolyCBD₂(PRF₂(r, j)))`. -/
def encYAt (j : Nat) : Prog isa := .seq (prfCbd j (yOff j)) (nttAt (yOff j))

/-- `u[i] = NTT⁻¹(Â[0, i] ŷ[0] + Â[1, i] ŷ[1] + Â[2, i] ŷ[2] + Â[3, i] ŷ[3]) + e₁[i]`,
into `ct + co + 352 i`. -/
def encUAt (ct : Reg) (co i : Nat) : Prog isa :=
  .seq (mulAt TP (aOff 0 i) (yOff 0)) <| .seq (mulAt PP (aOff 1 i) (yOff 1)) <| .seq (addAt TP PP) <|
  .seq (mulAt PP (aOff 2 i) (yOff 2)) <| .seq (addAt TP PP) <|
  .seq (mulAt PP (aOff 3 i) (yOff 3)) <| .seq (addAt TP PP) <| .seq (nttInvAt TP) <|
  .seq (prfCbd (4 + i) EP) <| .seq (addAt TP EP) (ceWAt TP 11 ct (co + 352 * i))

/-- `v = NTT⁻¹(t̂[0] ŷ[0] + t̂[1] ŷ[1] + t̂[2] ŷ[2] + t̂[3] ŷ[3]) + e₂ + μ`, with
`t̂` from `ek + eo` and `μ` from `m + mo`, into `ct + co + 1408`. -/
def encVAt (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
  .seq (dec12At ek eo TH) <| .seq (mulAt TP TH (yOff 0)) <|
  .seq (dec12At ek (eo + 384) TH) <| .seq (mulAt PP TH (yOff 1)) <| .seq (addAt TP PP) <|
  .seq (dec12At ek (eo + 768) TH) <| .seq (mulAt PP TH (yOff 2)) <| .seq (addAt TP PP) <|
  .seq (dec12At ek (eo + 1152) TH) <| .seq (mulAt PP TH (yOff 3)) <| .seq (addAt TP PP) <|
  .seq (nttInvAt TP) <| .seq (prfCbd 8 EP) <| .seq (addAt TP EP) <|
  .seq (ddAt m mo 1 EP) <| .seq (addAt TP EP) (ceWAt TP 5 ct (co + 1408))

/-- `ŷ`, `u` and `v`. -/
def encryptC (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
  .seq (encYAt 0) <| .seq (encYAt 1) <| .seq (encYAt 2) <| .seq (encYAt 3) <|
  .seq (encUAt ct co 0) <| .seq (encUAt ct co 1) <| .seq (encUAt ct co 2) <| .seq (encUAt ct co 3)
    (encVAt ek eo m mo ct co)

end VG.Impl.MlKem1024.AArch64

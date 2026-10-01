import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM-768 on AArch64: what `vg_mlkem768_encaps` and `vg_mlkem768_decaps` share

Both keep four pointers in `x25`–`x28` (`scratch` in `x28`), the AND of
`sample_ntt`'s results in `x24`, and save our caller's values of these and
of `x30` in `scratch` (`kemPrologue`, `kemEpilogue`): the Keccak functions
keep these registers, and restore the others they use from memory. Both run K-PKE.Encrypt (FIPS 203
Algorithm 14) after sampling `Â` (`(kemMatrixWith c)`, from `ρ ‖ j ‖ i` at `SB`):
`ŷ`, `u` and `v` (`(encryptCWith c)`), with `r` at `RB`, and `ek`, `m` and the
ciphertext wherever the caller says.

`scratch` (32 KiB) holds, at these offsets: the Keccak state (0) and working
space (200), `ρ ‖ j ‖ i` (840), `H(ek)` (880), `m'` (912), `r ‖ N` (944),
`K'` (984), `K̄` (1016), `PRF`'s output (1048), `sample_ntt`'s working space
(1176), the NTT's (3224), `Â` (4248, row by row), `ŷ` (13464), a noise
polynomial (16536), a sum of products (17560), a product (18584), `t̂[j]`
(19608), `c'` (20632), and the saved registers (21720).
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

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
def YH : Nat := 13464
def EP : Nat := 16536
def TP : Nat := 17560
def PP : Nat := 18584
def TH : Nat := 19608
def CB : Nat := 20632
def SV : Nat := 21720

/-- `Â[i, j]`. -/
def aOff (i j : Nat) : Nat := AH + 1024 * (3 * i + j)
/-- `ŷ[j]`. -/
def yOff (j : Nat) : Nat := YH + 1024 * j

end KEM

open KEM

/-! ## Registers -/

/-- The callee-saved register that keeps pointer `k` (`scratch` is `k = 3`). -/
def slotReg (k : Nat) : Reg := [Reg.x25, .x26, .x27, .x28].getD k .x28

/-- The register argument `b` comes in. -/
def argReg (b : Nat) : Reg := [Reg.x0, .x1, .x2, .x3, .x4].getD b .x5

/-- The registers saved in `scratch`, `x28` last. -/
def kemOwn : List Reg := [.x24, .x30, .x25, .x26, .x27, .x28]

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
def prfCbdWith (c : Impl.Sha3.AArch64.Callee) (N off : Nat) : Prog isa :=
  .seq (.block [.movz .x .x9 (BitVec.ofNat 16 N) 0, .strb .x9 .x28 (RB + 32)]) <|
  .seq (hashWith c .x28 ST WK 136 0x1f [⟨.x28, RB, 33⟩] [⟨.x28, PB, 128⟩]) <|
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

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `off` into `b + o`. -/
def ceAt (off d : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ (.movz .x .x1 (BitVec.ofNat 16 d) 0 :: ptrTo .x2 b o) ++
      ([.movz .x .x3 (BitVec.ofNat 16 (32 * d)) 0] : List Instr)))
    (.call "vg_mlkem_compress_encode" compressEncode)

/-- `Decompress_d(ByteDecode_d(b + o))` into the polynomial at `off`. -/
def ddAt (b : Reg) (o d off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ([.movz .x .x1 (BitVec.ofNat 16 (32 * d)) 0,
      .movz .x .x2 (BitVec.ofNat 16 d) 0] : List Instr) ++ ptrTo .x3 .x28 off))
    (.call "vg_mlkem_decode_decompress" decodeDecompress)

/-- `ByteDecode₁₂(b + o)` into the polynomial at `off`. -/
def dec12At (b : Reg) (o off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ptrTo .x1 .x28 off)) (.call "vg_mlkem_decode12" decode12)

/-! ## The matrix -/

/-- The seed `ρ ‖ j ‖ i` and the arguments of `SampleNTT` for `Â[i, j]`. -/
def kemSetup (i j : Nat) : List Instr :=
  [.movz .x .x9 (BitVec.ofNat 16 j) 0, .strb .x9 .x28 (SB + 32), .movz .x .x9 (BitVec.ofNat 16 i) 0,
    .strb .x9 .x28 (SB + 33)] ++ ptrTo .x0 .x28 SB ++ ptrTo .x1 .x28 (aOff i j) ++ ptrTo .x2 .x28 SS

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`, and its result ANDed into `x24`. -/
def kemSampleWith (c : Impl.Sha3.AArch64.Callee) (i j : Nat) : Prog isa := .seq (.block (kemSetup i j)) (kgCallWith c)

/-- The nine `SampleNTT`s, row by row. -/
def kemMatrixWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq ((kemSampleWith c) 0 0) <| .seq ((kemSampleWith c) 0 1) <| .seq ((kemSampleWith c) 0 2) <|
  .seq ((kemSampleWith c) 1 0) <| .seq ((kemSampleWith c) 1 1) <| .seq ((kemSampleWith c) 1 2) <|
  .seq ((kemSampleWith c) 2 0) <| .seq ((kemSampleWith c) 2 1) ((kemSampleWith c) 2 2)

/-! ## K-PKE.Encrypt after the matrix -/

/-- `ŷ[j] = NTT(SamplePolyCBD₂(PRF₂(r, j)))`. -/
def encYAtWith (c : Impl.Sha3.AArch64.Callee) (j : Nat) : Prog isa := .seq ((prfCbdWith c) j (yOff j)) (nttAt (yOff j))

/-- `u[i] = NTT⁻¹(Â[0, i] ŷ[0] + Â[1, i] ŷ[1] + Â[2, i] ŷ[2]) + e₁[i]`, into
`ct + co + 320 i`. -/
def encUAtWith (c : Impl.Sha3.AArch64.Callee) (ct : Reg) (co i : Nat) : Prog isa :=
  .seq (mulAt TP (aOff 0 i) (yOff 0)) <| .seq (mulAt PP (aOff 1 i) (yOff 1)) <| .seq (addAt TP PP) <|
  .seq (mulAt PP (aOff 2 i) (yOff 2)) <| .seq (addAt TP PP) <| .seq (nttInvAt TP) <|
  .seq ((prfCbdWith c) (3 + i) EP) <| .seq (addAt TP EP) (ceAt TP 10 ct (co + 320 * i))

/-- `v = NTT⁻¹(t̂[0] ŷ[0] + t̂[1] ŷ[1] + t̂[2] ŷ[2]) + e₂ + μ`, with `t̂` from
`ek + eo` and `μ` from `m + mo`, into `ct + co + 960`. -/
def encVAtWith (c : Impl.Sha3.AArch64.Callee) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
  .seq (dec12At ek eo TH) <| .seq (mulAt TP TH (yOff 0)) <|
  .seq (dec12At ek (eo + 384) TH) <| .seq (mulAt PP TH (yOff 1)) <| .seq (addAt TP PP) <|
  .seq (dec12At ek (eo + 768) TH) <| .seq (mulAt PP TH (yOff 2)) <| .seq (addAt TP PP) <|
  .seq (nttInvAt TP) <| .seq ((prfCbdWith c) 6 EP) <| .seq (addAt TP EP) <|
  .seq (ddAt m mo 1 EP) <| .seq (addAt TP EP) (ceAt TP 4 ct (co + 960))

/-- `ŷ`, `u` and `v`. -/
def encryptCWith (c : Impl.Sha3.AArch64.Callee) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
  .seq ((encYAtWith c) 0) <| .seq ((encYAtWith c) 1) <| .seq ((encYAtWith c) 2) <|
  .seq ((encUAtWith c) ct co 0) <| .seq ((encUAtWith c) ct co 1) <| .seq ((encUAtWith c) ct co 2) ((encVAtWith c) ek eo m mo ct co)

def prfCbd := prfCbdWith .scalar
def kemSample := kemSampleWith .scalar
def kemMatrix := kemMatrixWith .scalar
def encYAt := encYAtWith .scalar
def encUAt := encUAtWith .scalar
def encVAt := encVAtWith .scalar
def encryptC := encryptCWith .scalar

end VG.Impl.MlKem.AArch64

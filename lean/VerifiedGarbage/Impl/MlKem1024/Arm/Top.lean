import VerifiedGarbage.Impl.MlKem.Arm.Top
import VerifiedGarbage.Impl.MlKem1024.Arm.Poly

/-!
# ML-KEM-1024 on 32-bit ARM: key generation, encapsulation, decapsulation

The functions of ML-KEM-768 (`Impl/MlKem/Arm/Top.lean`, whose design this
follows, and whose building blocks this uses: `hash`, `copy`, `zeroPoly`,
the saving of our caller's registers, …) for `k = 4`, `d_u = 11` and
`d_v = 5`: `r7` is `scratch` throughout, `r4`, `r5`, `r6` and `r8` the
other buffers, `r9` and `r10` count loops and `r11` is the return value.
They save our caller's `r4`–`r11` and `lr` in `scratch`, so the only stack
they use is that of their calls' frames (8 bytes).

`scratch` holds the same values as ML-KEM-768's below offset 2048, and
uses its first 26144 bytes (of 49152):

* `2048 + 1024 k` for `k < 17`: polynomials (`oPoly`): `t̂` or `ŝ`
  (`k < 4`), `ŷ`, `û` or `ŝ` of key generation (`4 ≤ k < 8`), `ê` or `e₁`
  (`8 ≤ k < 12`), `e₂` or `v'` (12), `μ` (13), a sum (14), a product (15)
  and a sampled entry of `Â` (16);
* `19456`: the working space of `vg_mlkem_sample_ntt` (2048 bytes);
  `21504`: that of the NTTs and `vg_mlkem_multiply_ntts` (1024 bytes);
  `22528`: the ciphertext `c'` of decapsulation's re-encryption; `24576`: a
  copy of the ciphertext `c` of decapsulation.

The keys and ciphertexts are laid out as FIPS 203 says: `ek` is
`ByteEncode₁₂(t̂)` (1536 bytes) then `ρ`; `dk` is `ByteEncode₁₂(ŝ)`, `ek`
(at 1536), `H(ek)` (at 3104) and `z` (at 3136); `c` is the four
`ByteEncode₁₁(Compress₁₁(u[i]))` (352 bytes each) then
`ByteEncode₅(Compress₅(v))` (at 1408).
-/

namespace VG.Impl.MlKem1024.Arm

open VG.Arm
open VG.Impl.MlKem.Arm (oWork oSave oExtra oG oSigma oHek oMsg oPrf oK oKbar oSeed oPoly ptrTo slotAt
  at384 count Piece hash copy zeroPoly callAdd callSub callMul callNtt callNttInv callCbd2 callEncode12
  callDecode12 callCompress callDecompress callSample seedBytes topEnd encapsSetup decapsSetup
  selSetup selBody cmpBody saveRegs)

/-! ## The layout of `scratch` -/

abbrev oAcc4 : Nat := oPoly 14
abbrev oTmp4 : Nat := oPoly 15
abbrev oAhat4 : Nat := oPoly 16
abbrev oSample4 : Nat := 19456
abbrev oNtt4 : Nat := 21504
abbrev oCt4 : Nat := 22528
abbrev oCin4 : Nat := 24576

/-- `d ← b + 352 c`. -/
def at352 (d b c : Reg) : List Instr :=
  [.dp .add d b (.shifted c .lsl 8), .dp .add d d (.shifted c .lsl 6), .dp .add d d (.shifted c .lsl 5)]

def callCompress4 : Prog isa := .call "vg_mlkem1024_compress_encode" compressEncode1024
def callDecompress4 : Prog isa := .call "vg_mlkem1024_decode_decompress" decodeDecompress1024

/-! ## Sampling -/

/-- `SamplePolyCBD₂(PRF₂(σ, N))` into polynomial `4 + N`, with `N` in `r9`
(and `σ ‖ N` at `920`), then its NTT if `withNtt`. -/
def prfBody4 (withNtt : Bool) (N₁ : Nat) : Prog isa :=
  .seq (.block [.strb .r9 .r7 (oSigma + 32)]) <|
  .seq (hash 136 0x1f [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩]) <|
  .seq (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly 4))) <|
  .seq callCbd2 <|
  .seq (if withNtt then .seq (.block (slotAt .r0 .r9 (oPoly 4) ++ [ptrTo .r1 .r7 oNtt4])) callNtt else .block [])
    (.block (count .r9 N₁))

/-- `prfBody4` for `N` from `N₀` to `N₁ - 1`. -/
def prfLoop4 (withNtt : Bool) (N₀ N₁ : Nat) : Prog isa :=
  .seq (.block [.mov .r9 (.imm (BitVec.ofNat 32 N₀))]) (.loop (prfBody4 withNtt N₁) .ne)

/-- Entry `j` of row `i` (in `r10` and `r9`) of `Â` (or of `Â^⊺`) sampled,
and its product with polynomial `4 + j` added to the sum. -/
def rowBody4 (transpose : Bool) : Prog isa :=
  .seq (.block (seedBytes transpose ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 oAhat4, ptrTo .r2 .r7 oSample4])) <|
  .seq callSample <|
  .seq (.block [.dp .and .r11 .r11 (.reg .r0), .cmp .r0 (.imm 0)]) <|
  .seq (.ite .eq (.block (slotAt .r1 .r10 (oPoly 4))) (.block [ptrTo .r1 .r7 oAhat4])) <|
  .seq (.block (ptrTo .r0 .r7 oTmp4 :: slotAt .r2 .r10 (oPoly 4) ++ [ptrTo .r3 .r7 oNtt4])) <|
  .seq callMul <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 oTmp4]) <|
  .seq callAdd (.block (count .r10 4))

/-- Row `i` of `Â ∘ v̂` (or of `Â^⊺ ∘ v̂`), `v̂` polynomials 4 to 7, into
polynomial 14. -/
def rowSum4 (transpose : Bool) : Prog isa :=
  .seq (zeroPoly oAcc4) (.seq (.block [.mov .r10 (.imm 0)]) (.loop (rowBody4 transpose) .ne))

def dotBody4 : Prog isa :=
  .seq (.block (ptrTo .r0 .r7 oTmp4 :: slotAt .r1 .r10 (oPoly 0) ++ slotAt .r2 .r10 (oPoly 4) ++
    [ptrTo .r3 .r7 oNtt4])) <|
  .seq callMul <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 oTmp4]) <|
  .seq callAdd (.block (count .r10 4))

/-- The sum of the products of polynomials `j` and `4 + j`, into polynomial
14. -/
def dotP4 : Prog isa := .seq (zeroPoly oAcc4) (.seq (.block [.mov .r10 (.imm 0)]) (.loop dotBody4 .ne))

/-! ## `vg_mlkem1024_keygen(seed = r0, ek = r1, dk = r2, scratch = r3) -> r0` -/

def kgSetup4 : List Instr :=
  saveRegs .r3 oSave ++
    ([.str .lr .r3 (oSave + 32), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r7 (.reg .r3), .mov .r12 (.imm 4), .strb .r12 .r3 oK] : List Instr)

/-- Row `i` (in `r9`) of `t̂ = Â ∘ ŝ + ê`, encoded into `ek`. -/
def kgRowBody4 : Prog isa :=
  .seq (rowSum4 false) <|
  .seq (.block (ptrTo .r0 .r7 oAcc4 :: slotAt .r1 .r9 (oPoly 8))) <|
  .seq callAdd <|
  .seq (.block (ptrTo .r0 .r7 oAcc4 :: at384 .r1 .r5 .r9)) <|
  .seq callEncode12 (.block (count .r9 4))

/-- `ŝ[j]` (`j` in `r9`) encoded into `dk`. -/
def kgSBody4 : Prog isa :=
  .seq (.block (slotAt .r0 .r9 (oPoly 4) ++ at384 .r1 .r6 .r9)) (.seq callEncode12 (.block (count .r9 4)))

def keygen1024 : Prog isa :=
  .seq (.block kgSetup4) <|
  .seq (hash 72 0x06 [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (copy .r7 oG .r7 oSeed 32) <|
  .seq (prfLoop4 true 0 8) <|
  .seq (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) <|
  .seq (.loop kgRowBody4 .ne) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop kgSBody4 .ne) <|
  .seq (copy .r7 oSeed .r5 1536 32) <|
  .seq (copy .r5 0 .r6 1536 1568) <|
  .seq (hash 136 0x06 [⟨.r5, 0, 1568⟩] [⟨.r6, 3104, 32⟩]) <|
  .seq (copy .r4 32 .r6 3136 32) (.block topEnd)

/-! ## K-PKE.Encrypt, with `ek` in `r4`, `m` in `r5`, `r` at `920` and `c` to `r8` -/

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (`i` in `r9`). -/
def decTBody4 : Prog isa :=
  .seq (.block (at384 .r0 .r4 .r9 ++ slotAt .r1 .r9 (oPoly 0))) (.seq callDecode12 (.block (count .r9 4)))

/-- `u[i]` (`i` in `r9`), compressed and encoded into `c`. -/
def encRowBody4 : Prog isa :=
  .seq (rowSum4 true) <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 oNtt4]) <|
  .seq callNttInv <|
  .seq (.block (ptrTo .r0 .r7 oAcc4 :: slotAt .r1 .r9 (oPoly 8))) <|
  .seq callAdd <|
  .seq (.block ([ptrTo .r0 .r7 oAcc4, .mov .r1 (.imm 11)] ++ at352 .r2 .r8 .r9 ++ [.mov .r3 (.imm 352)])) <|
  .seq callCompress4 (.block (count .r9 4))

def encrypt4 : Prog isa :=
  .seq (copy .r4 1536 .r7 oSeed 32) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop decTBody4 .ne) <|
  .seq (prfLoop4 true 0 4) <|
  .seq (prfLoop4 false 4 9) <|
  .seq (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly 13)]) <|
  .seq callDecompress <|
  .seq (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) <|
  .seq (.loop encRowBody4 .ne) <|
  .seq dotP4 <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 oNtt4]) <|
  .seq callNttInv <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 (oPoly 12)]) <|
  .seq callAdd <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 (oPoly 13)]) <|
  .seq callAdd <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, .mov .r1 (.imm 5), ptrTo .r2 .r8 1408, .mov .r3 (.imm 160)]) callCompress4

/-! ## `vg_mlkem1024_encaps(ek = r0, m = r1, key = r2, ct = r3, scratch = [sp]) -> r0` -/

def encaps1024 : Prog isa :=
  .seq (.block [.ldrSp .r12 0]) <|
  .seq (.block encapsSetup) <|
  .seq (copy .r5 0 .r7 oMsg 32) <|
  .seq (.block [ptrTo .r5 .r7 oMsg]) <|
  .seq (hash 136 0x06 [⟨.r4, 0, 1568⟩] [⟨.r7, oHek, 32⟩]) <|
  .seq (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (copy .r7 oG .r6 0 32) <|
  .seq encrypt4 (.block topEnd)

/-! ## `vg_mlkem1024_decaps(dk = r0, ct = r1, key = r2, scratch = r3) -> r0` -/

/-- `û[i] = NTT(Decompress₁₁(ByteDecode₁₁(c[352i : 352i + 352])))` (`i` in `r9`). -/
def decUBody4 : Prog isa :=
  .seq (.block (at352 .r0 .r6 .r9 ++ [.mov .r1 (.imm 352), .mov .r2 (.imm 11)] ++ slotAt .r3 .r9 (oPoly 4))) <|
  .seq callDecompress4 <|
  .seq (.block (slotAt .r0 .r9 (oPoly 4) ++ [ptrTo .r1 .r7 oNtt4])) <|
  .seq callNtt (.block (count .r9 4))

/-- K-PKE.Decrypt, with `dk` in `r4` and `c` in `r6`: `m'` to `992`. -/
def decrypt4 : Prog isa :=
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop decUBody4 .ne) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop decTBody4 .ne) <|
  .seq dotP4 <|
  .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 oNtt4]) <|
  .seq callNttInv <|
  .seq (.block [ptrTo .r0 .r6 1408, .mov .r1 (.imm 160), .mov .r2 (.imm 5), ptrTo .r3 .r7 (oPoly 12)]) <|
  .seq callDecompress4 <|
  .seq (.block [ptrTo .r0 .r7 (oPoly 12), ptrTo .r1 .r7 oAcc4]) <|
  .seq callSub <|
  .seq (.block [ptrTo .r0 .r7 (oPoly 12), .mov .r1 (.imm 1), ptrTo .r2 .r7 oMsg, .mov .r3 (.imm 32)]) callCompress

/-- The OR of the XORs of the bytes of `c` (`r6`) and `c'`, into `r12`. -/
def compare4 : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r6), ptrTo .r1 .r7 oCt4, .mov .r12 (.imm 0), .mov .r9 (.imm 1568)])
    (.loop (.block cmpBody) .ne)

def decaps1024 : Prog isa :=
  .seq (.block decapsSetup) <|
  .seq (copy .r6 0 .r7 oCin4 1568) <|
  .seq (.block [ptrTo .r6 .r7 oCin4]) <|
  .seq decrypt4 <|
  .seq (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r4, 3104, 32⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (hash 136 0x1f [⟨.r4, 3136, 32⟩, ⟨.r7, oCin4, 1568⟩] [⟨.r7, oKbar, 32⟩]) <|
  .seq (.block [ptrTo .r4 .r4 1536, ptrTo .r5 .r7 oMsg, ptrTo .r8 .r7 oCt4]) <|
  .seq encrypt4 <|
  .seq compare4 <|
  .seq (.block selSetup) <|
  .seq (.loop (.block selBody) .ne) (.block topEnd)

end VG.Impl.MlKem1024.Arm

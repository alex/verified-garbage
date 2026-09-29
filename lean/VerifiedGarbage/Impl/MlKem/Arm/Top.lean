import VerifiedGarbage.Impl.MlKem.Arm.Sample

/-!
# ML-KEM-768 on 32-bit ARM: key generation, encapsulation, decapsulation

The top-level functions are sequences of calls of the verified primitives
and SHA-3 functions, on buffers at fixed offsets in `scratch` (32 KiB) and
in the arguments. They keep the pointers in callee-saved registers, which
the callees preserve: `r7` is `scratch` throughout, and `r4`, `r5`, `r6`
and `r8` the other buffers; `r9` and `r10` count loops and `r11` is the
return value: 1, or 0 once a `SampleNTT` has not finished within 280
iterations. They save our caller's `r4`–`r11` and `lr` in `scratch`, so the
only stack they use is that of their calls' frames (8 bytes).

`scratch` holds, at these offsets:

* `0`: the Keccak state; `200`: the working space of the sponge functions;
* `840`: our caller's `r4`–`r11` and `lr`; `876`: the pointer `key` of
  `vg_mlkem768_decaps`;
* `888`: the 64 bytes of `G`, `ρ ‖ σ` or `K ‖ r` (each hash has one output,
  squeezed at once), so `σ` (or `r`) is at `920`, the seed of `PRF`, followed
  by its counter `N`; `960`: `H(ek)`; `992`: the message: a copy of `m`
  in encapsulation, `m'` in decapsulation; `1024`: the 128 bytes of a `PRF`; `1152`: the byte `k` of
  `G(d ‖ k)`; `1184`: `K̄`; `1216`: the seed `ρ ‖ j ‖ i` of `SampleNTT`;
* `2048 + 1024 k` for `k < 14`: polynomials (`oPoly`): `t̂` or `ŝ` (`k < 3`),
  `ŷ`, `û` or `ŝ` of key generation (`3 ≤ k < 6`), `ê` or `e₁`
  (`6 ≤ k < 9`), `e₂` or `v'` (9), `μ` (10), a sum (11), a product (12) and
  a sampled entry of `Â` (13);
* `16384`: the working space of `vg_mlkem_sample_ntt` (2048 bytes);
  `18432`: that of the NTTs and `vg_mlkem_multiply_ntts` (1024 bytes);
  `19456`: the ciphertext `c'` of decapsulation's re-encryption; `24576`: a
  copy of the ciphertext `c` of decapsulation.

The inputs a function only reads may overlap each other (the contracts let
them), so where a function reads two of them, it first copies one into
`scratch` (`m` in encapsulation, `c` in decapsulation), and works on the copy.

`hash` computes a SHA-3 or SHAKE function: the Keccak state set to zero,
each piece of the message absorbed in turn (each from the position the
previous one returned), the padding, and each piece of output squeezed in
turn. A row of `Â ∘ v̂` (or of `Â^⊺ ∘ v̂`) is summed from zero (`rowSum`),
each entry of `Â` sampled into the same buffer; if its `SampleNTT` does not
finish, `r0 = 0`, the return value becomes 0, and the product uses `v̂[j]`
in its place, so every polynomial stays reduced. Whether a `SampleNTT`
finishes depends only on its seed, which is public: `ρ` (which the
contracts let the functions leak) and two indices. Decapsulation compares
`c` and `c'` by the OR of the XORs of their bytes, and selects `K'` or `K̄`
by a mask, in constant time.
-/

namespace VG.Impl.MlKem.Arm

open VG.Arm

/-! ## The layout of `scratch` -/

abbrev oWork : Nat := 200
abbrev oSave : Nat := 840
abbrev oExtra : Nat := 876
abbrev oG : Nat := 888
abbrev oSigma : Nat := 920
abbrev oHek : Nat := 960
abbrev oMsg : Nat := 992
abbrev oPrf : Nat := 1024
abbrev oK : Nat := 1152
abbrev oKbar : Nat := 1184
abbrev oSeed : Nat := 1216
/-- The polynomial `k`. -/
abbrev oPoly (k : Nat) : Nat := 2048 + 1024 * k
abbrev oAcc : Nat := oPoly 11
abbrev oTmp : Nat := oPoly 12
abbrev oAhat : Nat := oPoly 13
abbrev oSample : Nat := 16384
abbrev oNtt : Nat := 18432
abbrev oCt : Nat := 19456
abbrev oCin : Nat := 24576

/-! ## Building blocks -/

/-- `d ← b + off`. -/
def ptrTo (d b : Reg) (off : Nat) : Instr := .dp .add d b (.imm (BitVec.ofNat 32 off))

/-- `d ← r7 + 1024 c + off`: polynomial `c` of an array of them at `off` in
`scratch`. -/
def slotAt (d c : Reg) (off : Nat) : List Instr :=
  [.dp .add d .r7 (.shifted c .lsl 10), ptrTo d d off]

/-- `d ← b + 384 c`. -/
def at384 (d b c : Reg) : List Instr := [.dp .add d b (.shifted c .lsl 8), .dp .add d d (.shifted c .lsl 7)]

/-- `d ← b + 320 c`. -/
def at320 (d b c : Reg) : List Instr := [.dp .add d b (.shifted c .lsl 8), .dp .add d d (.shifted c .lsl 6)]

/-- The counter `c` incremented, and `Z` set when it reaches `n`. -/
def count (c : Reg) (n : Nat) : List Instr := [.dp .add c c (.imm 1), .cmp c (.imm (BitVec.ofNat 32 n))]

/-- A buffer: `off` bytes past the pointer in `base`, of `len` bytes. -/
structure Piece where
  base : Reg
  off : Nat
  len : Nat

/-- The Keccak state, the rate and the working space in `r0`, `r1` and
`lr`, and the position in `r2`: 0 at `first`, or the position the previous
call returned. -/
def keccakArgs (rate : Nat) (first : Bool) : List Instr :=
  (if first then [.mov .r2 (.imm 0)] else [.mov .r2 (.reg .r0)]) ++
    [.mov .r0 (.reg .r7), .mov .r1 (.imm (BitVec.ofNat 32 rate)), ptrTo .lr .r7 oWork]

/-- The piece `p` in `r3` and its length in `r12`. -/
def pieceArgs (p : Piece) : List Instr := [ptrTo .r3 p.base p.off, .mov .r12 (.imm (BitVec.ofNat 32 p.len))]

/-- Absorb the pieces `ps`. -/
def absorbs (rate : Nat) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (keccakArgs rate first ++ pieceArgs p)) (.seq absorbCall (absorbs rate false ps))

/-- Squeeze into the pieces `ps`. -/
def squeezes (rate : Nat) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps => .seq (.block (keccakArgs rate first ++ pieceArgs p)) (.seq squeezeCall (squeezes rate false ps))

/-- The hash of the message `ins` (pieces, absorbed after one another) into
`outs`, with the rate `rate` and the domain-separation suffix `sfx`. -/
def hash (rate sfx : Nat) (ins outs : List Piece) : Prog isa :=
  .seq (.block (zeroState .r7)) <|
  .seq (absorbs rate true ins) <|
  .seq (.block (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr)))
    (.seq padCall (squeezes rate true outs))

def copyBody : List Instr :=
  [.ldrb .r3 .r0 0, .strb .r3 .r1 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1),
   .subs .r2 .r2 (.imm 1)]

/-- Copy `len` bytes from `sb + so` to `db + dO`. -/
def copy (sb : Reg) (so : Nat) (db : Reg) (dO len : Nat) : Prog isa :=
  .seq (.block [ptrTo .r0 sb so, ptrTo .r1 db dO, .mov .r2 (.imm (BitVec.ofNat 32 len))])
    (.loop (.block copyBody) .ne)

def zeroBody : List Instr := [.str .r1 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r2 .r2 (.imm 1)]

/-- The polynomial at `off` in `scratch` set to zero. -/
def zeroPoly (off : Nat) : Prog isa :=
  .seq (.block [ptrTo .r0 .r7 off, .mov .r1 (.imm 0), .mov .r2 (.imm 256)]) (.loop (.block zeroBody) .ne)

/-! ## The primitives -/

def callAdd : Prog isa := .call "vg_mlkem_add" add
def callSub : Prog isa := .call "vg_mlkem_sub" sub
def callMul : Prog isa := .call "vg_mlkem_multiply_ntts" multiplyNTTs
def callNtt : Prog isa := .call "vg_mlkem_ntt" ntt
def callNttInv : Prog isa := .call "vg_mlkem_ntt_inv" nttInv
def callCbd2 : Prog isa := .call "vg_mlkem_cbd2" cbd2
def callEncode12 : Prog isa := .call "vg_mlkem_encode12" encode12
def callDecode12 : Prog isa := .call "vg_mlkem_decode12" decode12
def callCompress : Prog isa := .call "vg_mlkem_compress_encode" compressEncode
def callDecompress : Prog isa := .call "vg_mlkem_decode_decompress" decodeDecompress
def callSample : Prog isa := .call "vg_mlkem_sample_ntt" sampleNTT

/-! ## Sampling -/

/-- `SamplePolyCBD₂(PRF₂(σ, N))` into polynomial `3 + N`, with `N` in `r9`
(and `σ ‖ N` at `920`), then its NTT if `withNtt`. -/
def prfBody (withNtt : Bool) (N₁ : Nat) : Prog isa :=
  .seq (.block [.strb .r9 .r7 (oSigma + 32)]) <|
  .seq (hash 136 0x1f [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩]) <|
  .seq (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly 3))) <|
  .seq callCbd2 <|
  .seq (if withNtt then .seq (.block (slotAt .r0 .r9 (oPoly 3) ++ [ptrTo .r1 .r7 oNtt])) callNtt else .block [])
    (.block (count .r9 N₁))

/-- `prfBody` for `N` from `N₀` to `N₁ - 1`. -/
def prfLoop (withNtt : Bool) (N₀ N₁ : Nat) : Prog isa :=
  .seq (.block [.mov .r9 (.imm (BitVec.ofNat 32 N₀))]) (.loop (prfBody withNtt N₁) .ne)

/-- The indices of the seed: `ρ ‖ j ‖ i` for `Â[i, j]`, with `i` in `r9` and
`j` in `r10`, or `ρ ‖ i ‖ j` for `Â[j, i]` (`transpose`). -/
def seedBytes (transpose : Bool) : List Instr :=
  if transpose then [.strb .r9 .r7 (oSeed + 32), .strb .r10 .r7 (oSeed + 33)]
  else [.strb .r10 .r7 (oSeed + 32), .strb .r9 .r7 (oSeed + 33)]

/-- Entry `j` of row `i` (in `r10` and `r9`) of `Â` (or of `Â^⊺`) sampled,
and its product with polynomial `3 + j` added to the sum. -/
def rowBody (transpose : Bool) : Prog isa :=
  .seq (.block (seedBytes transpose ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 oAhat, ptrTo .r2 .r7 oSample])) <|
  .seq callSample <|
  .seq (.block [.dp .and .r11 .r11 (.reg .r0), .cmp .r0 (.imm 0)]) <|
  .seq (.ite .eq (.block (slotAt .r1 .r10 (oPoly 3))) (.block [ptrTo .r1 .r7 oAhat])) <|
  .seq (.block (ptrTo .r0 .r7 oTmp :: slotAt .r2 .r10 (oPoly 3) ++ [ptrTo .r3 .r7 oNtt])) <|
  .seq callMul <|
  .seq (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 oTmp]) <|
  .seq callAdd (.block (count .r10 3))

/-- Row `i` of `Â ∘ v̂` (or of `Â^⊺ ∘ v̂`), `v̂` polynomials 3 to 5, into
polynomial 11. -/
def rowSum (transpose : Bool) : Prog isa :=
  .seq (zeroPoly oAcc) (.seq (.block [.mov .r10 (.imm 0)]) (.loop (rowBody transpose) .ne))

def dotBody : Prog isa :=
  .seq (.block (ptrTo .r0 .r7 oTmp :: slotAt .r1 .r10 (oPoly 0) ++ slotAt .r2 .r10 (oPoly 3) ++
    [ptrTo .r3 .r7 oNtt])) <|
  .seq callMul <|
  .seq (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 oTmp]) <|
  .seq callAdd (.block (count .r10 3))

/-- The sum of the products of polynomials `j` and `3 + j`, into polynomial
11. -/
def dot : Prog isa := .seq (zeroPoly oAcc) (.seq (.block [.mov .r10 (.imm 0)]) (.loop dotBody .ne))

/-! ## Saving our caller's registers -/

/-- The return value, and our caller's registers restored. -/
def topEnd : List Instr :=
  [.mov .r0 (.reg .r11), .mov .r3 (.reg .r7)] ++ restoreRegs .r3 oSave ++ ([.ldr .lr .r3 (oSave + 32)] : List Instr)

/-! ## `vg_mlkem768_keygen(seed = r0, ek = r1, dk = r2, scratch = r3) -> r0` -/

def kgSetup : List Instr :=
  saveRegs .r3 oSave ++
    ([.str .lr .r3 (oSave + 32), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r7 (.reg .r3), .mov .r12 (.imm 3), .strb .r12 .r3 oK] : List Instr)

/-- Row `i` (in `r9`) of `t̂ = Â ∘ ŝ + ê`, encoded into `ek`. -/
def kgRowBody : Prog isa :=
  .seq (rowSum false) <|
  .seq (.block (ptrTo .r0 .r7 oAcc :: slotAt .r1 .r9 (oPoly 6))) <|
  .seq callAdd <|
  .seq (.block (ptrTo .r0 .r7 oAcc :: at384 .r1 .r5 .r9)) <|
  .seq callEncode12 (.block (count .r9 3))

/-- `ŝ[j]` (`j` in `r9`) encoded into `dk`. -/
def kgSBody : Prog isa :=
  .seq (.block (slotAt .r0 .r9 (oPoly 3) ++ at384 .r1 .r6 .r9)) (.seq callEncode12 (.block (count .r9 3)))

def keygen : Prog isa :=
  .seq (.block kgSetup) <|
  .seq (hash 72 0x06 [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (copy .r7 oG .r7 oSeed 32) <|
  .seq (prfLoop true 0 6) <|
  .seq (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) <|
  .seq (.loop kgRowBody .ne) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop kgSBody .ne) <|
  .seq (copy .r7 oSeed .r5 1152 32) <|
  .seq (copy .r5 0 .r6 1152 1184) <|
  .seq (hash 136 0x06 [⟨.r5, 0, 1184⟩] [⟨.r6, 2336, 32⟩]) <|
  .seq (copy .r4 32 .r6 2368 32) (.block topEnd)

/-! ## K-PKE.Encrypt, with `ek` in `r4`, `m` in `r5`, `r` at `920` and `c` to `r8` -/

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (`i` in `r9`). -/
def decTBody : Prog isa :=
  .seq (.block (at384 .r0 .r4 .r9 ++ slotAt .r1 .r9 (oPoly 0))) (.seq callDecode12 (.block (count .r9 3)))

/-- `u[i]` (`i` in `r9`), compressed and encoded into `c`. -/
def encRowBody : Prog isa :=
  .seq (rowSum true) <|
  .seq (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 oNtt]) <|
  .seq callNttInv <|
  .seq (.block (ptrTo .r0 .r7 oAcc :: slotAt .r1 .r9 (oPoly 6))) <|
  .seq callAdd <|
  .seq (.block ([ptrTo .r0 .r7 oAcc, .mov .r1 (.imm 10)] ++ at320 .r2 .r8 .r9 ++ [.mov .r3 (.imm 320)])) <|
  .seq callCompress (.block (count .r9 3))

def encrypt : Prog isa :=
  .seq (copy .r4 1152 .r7 oSeed 32) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop decTBody .ne) <|
  .seq (prfLoop true 0 3) <|
  .seq (prfLoop false 3 7) <|
  .seq (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly 10)]) <|
  .seq callDecompress <|
  .seq (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) <|
  .seq (.loop encRowBody .ne) <|
  .seq dot <|
  .seq (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 oNtt]) <|
  .seq callNttInv <|
  .seq (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 (oPoly 9)]) <|
  .seq callAdd <|
  .seq (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 (oPoly 10)]) <|
  .seq callAdd <|
  .seq (.block [ptrTo .r0 .r7 oAcc, .mov .r1 (.imm 4), ptrTo .r2 .r8 960, .mov .r3 (.imm 128)]) callCompress

/-! ## `vg_mlkem768_encaps(ek = r0, m = r1, key = r2, ct = r3, scratch = [sp]) -> r0` -/

/-- After `scratch` loaded into `r12` from the stack. -/
def encapsSetup : List Instr :=
  saveRegs .r12 oSave ++
    ([.str .lr .r12 (oSave + 32), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r8 (.reg .r3), .mov .r7 (.reg .r12)] : List Instr)

def encaps : Prog isa :=
  .seq (.block [.ldrSp .r12 0]) <|
  .seq (.block encapsSetup) <|
  .seq (copy .r5 0 .r7 oMsg 32) <|
  .seq (.block [ptrTo .r5 .r7 oMsg]) <|
  .seq (hash 136 0x06 [⟨.r4, 0, 1184⟩] [⟨.r7, oHek, 32⟩]) <|
  .seq (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (copy .r7 oG .r6 0 32) <|
  .seq encrypt (.block topEnd)

/-! ## `vg_mlkem768_decaps(dk = r0, ct = r1, key = r2, scratch = r3) -> r0` -/

def decapsSetup : List Instr :=
  saveRegs .r3 oSave ++
    ([.str .lr .r3 (oSave + 32), .str .r2 .r3 oExtra, .mov .r4 (.reg .r0), .mov .r6 (.reg .r1),
      .mov .r7 (.reg .r3)] : List Instr)

/-- `û[i] = NTT(Decompress₁₀(ByteDecode₁₀(c[320i : 320i + 320])))` (`i` in `r9`). -/
def decUBody : Prog isa :=
  .seq (.block (at320 .r0 .r6 .r9 ++ [.mov .r1 (.imm 320), .mov .r2 (.imm 10)] ++ slotAt .r3 .r9 (oPoly 3))) <|
  .seq callDecompress <|
  .seq (.block (slotAt .r0 .r9 (oPoly 3) ++ [ptrTo .r1 .r7 oNtt])) <|
  .seq callNtt (.block (count .r9 3))

/-- K-PKE.Decrypt, with `dk` in `r4` and `c` in `r6`: `m'` to `992`. -/
def decrypt : Prog isa :=
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop decUBody .ne) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop decTBody .ne) <|
  .seq dot <|
  .seq (.block [ptrTo .r0 .r7 oAcc, ptrTo .r1 .r7 oNtt]) <|
  .seq callNttInv <|
  .seq (.block [ptrTo .r0 .r6 960, .mov .r1 (.imm 128), .mov .r2 (.imm 4), ptrTo .r3 .r7 (oPoly 9)]) <|
  .seq callDecompress <|
  .seq (.block [ptrTo .r0 .r7 (oPoly 9), ptrTo .r1 .r7 oAcc]) <|
  .seq callSub <|
  .seq (.block [ptrTo .r0 .r7 (oPoly 9), .mov .r1 (.imm 1), ptrTo .r2 .r7 oMsg, .mov .r3 (.imm 32)]) callCompress

def cmpBody : List Instr :=
  [.ldrb .r2 .r0 0, .ldrb .r3 .r1 0, .dp .eor .r2 .r2 (.reg .r3), .dp .orr .r12 .r12 (.reg .r2),
   .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1), .subs .r9 .r9 (.imm 1)]

/-- The OR of the XORs of the bytes of `c` (`r6`) and `c'`, into `r12`. -/
def compare : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r6), ptrTo .r1 .r7 oCt, .mov .r12 (.imm 0), .mov .r9 (.imm 1088)])
    (.loop (.block cmpBody) .ne)

/-- A mask in `r12` (all ones if `c = c'`); `r0`, `r1` and `r2` point to
`K'`, `K̄` and `key`. -/
def selSetup : List Instr :=
  [.dp .sub .r12 .r12 (.imm 1), .mov .r12 (.shifted .r12 .lsr 31), .mov .r3 (.imm 0),
   .dp .sub .r12 .r3 (.reg .r12), ptrTo .r0 .r7 oG, ptrTo .r1 .r7 oKbar, .ldr .r2 .r7 oExtra, .mov .r9 (.imm 32)]

/-- `key[i] = K̄[i] ^ ((K'[i] ^ K̄[i]) & mask)`. -/
def selBody : List Instr :=
  [.ldrb .r3 .r0 0, .ldrb .r10 .r1 0, .dp .eor .r3 .r3 (.reg .r10), .dp .and .r3 .r3 (.reg .r12),
   .dp .eor .r3 .r3 (.reg .r10), .strb .r3 .r2 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1),
   .dp .add .r2 .r2 (.imm 1), .subs .r9 .r9 (.imm 1)]

def decaps : Prog isa :=
  .seq (.block decapsSetup) <|
  .seq (copy .r6 0 .r7 oCin 1088) <|
  .seq (.block [ptrTo .r6 .r7 oCin]) <|
  .seq decrypt <|
  .seq (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r4, 2336, 32⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (hash 136 0x1f [⟨.r4, 2368, 32⟩, ⟨.r6, 0, 1088⟩] [⟨.r7, oKbar, 32⟩]) <|
  .seq (.block [ptrTo .r4 .r4 1152, ptrTo .r5 .r7 oMsg, ptrTo .r8 .r7 oCt]) <|
  .seq encrypt <|
  .seq compare <|
  .seq (.block selSetup) <|
  .seq (.loop (.block selBody) .ne) (.block topEnd)

end VG.Impl.MlKem.Arm

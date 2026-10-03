import VerifiedGarbage.Impl.MlKem.Arm.Sample
import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on 32-bit ARM: key generation, encapsulation, decapsulation

The top-level functions of ML-KEM-768 and ML-KEM-1024, for any parameter set
`K : KemLay` (`k`, `d_u`, `d_v` and the primitives compressing to `d_u` and
`d_v` bits): ML-KEM-768's (`kl768`) are here, ML-KEM-1024's in
`Impl/MlKem1024/Arm/Top.lean`. They are sequences of calls of the verified
primitives and SHA-3 functions, on buffers at fixed offsets in `scratch` (of
which they use less than 32 KiB) and in the arguments. They keep the pointers
in callee-saved registers, which the callees preserve: `r7` is `scratch`
throughout, and `r4`, `r5`, `r6` and `r8` the other buffers; `r9` and `r10`
count loops and `r11` is the return value: 1, or 0 once a `SampleNTT` has
not finished within 280 iterations. They save our caller's `r4`–`r11` and
`lr` in `scratch`, so the only stack they use is that of their calls' frames
(8 bytes).

`scratch` holds, at these offsets:

* `0`: the Keccak state; `200`: the working space of the sponge functions;
* `840`: our caller's `r4`–`r11` and `lr`; `876`: the pointer `key` of
  decapsulation;
* `888`: the 64 bytes of `G`, `ρ ‖ σ` or `K ‖ r` (each hash has one output,
  squeezed at once), so `σ` (or `r`) is at `920`, the seed of `PRF`, followed
  by its counter `N`; `960`: `H(ek)`; `992`: the message: a copy of `m`
  in encapsulation, `m'` in decapsulation; `1024`: the 128 bytes of a `PRF`; `1152`: the byte `k` of
  `G(d ‖ k)`; `1184`: `K̄`; `1216`: the seed `ρ ‖ j ‖ i` of `SampleNTT`;
* `2048 + 1024 j` for `j < 3k + 5`: polynomials (`oPoly`): `t̂` or `ŝ`
  (`j < k`), `ŷ`, `û` or `ŝ` of key generation (`k ≤ j < 2k`), `ê` or `e₁`
  (`2k ≤ j < 3k`), `e₂` or `v'` (`3k`), `μ` (`3k + 1`), a sum (`3k + 2`), a
  product (`3k + 3`) and a sampled entry of `Â` (`3k + 4`);
* polynomial `3k + 5` on: the working space of `vg_mlkem_sample_ntt` (2048
  bytes), then that of the NTTs and `vg_mlkem_multiply_ntts` (1024 bytes),
  then the ciphertext `c'` of decapsulation's re-encryption (`KemLay.oSample`,
  `oNtt`, `oCt`); `24576`: a copy of the ciphertext `c` of decapsulation.

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

/-- `d ← b + (2^{s₀} + 2^{s₁} + ⋯) c`, for the shifts `s₀ :: ss`. -/
def atShifts (d b c : Reg) : List Nat → List Instr
  | [] => []
  | s₀ :: ss => .dp .add d b (.shifted c .lsl s₀) :: ss.map fun s => .dp .add d d (.shifted c .lsl s)

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
def callNttInv : Prog isa := .call "vg_mlkem_inv_ntt" nttInv
def callCbd2 : Prog isa := .call "vg_mlkem_cbd2" cbd2
def callEncode12 : Prog isa := .call "vg_mlkem_encode12" encode12
def callDecode12 : Prog isa := .call "vg_mlkem_decode12" decode12
def callCompress : Prog isa := .call "vg_mlkem_compress_encode" compressEncode
def callDecompress : Prog isa := .call "vg_mlkem_decode_decompress" decodeDecompress
def callSample : Prog isa := .call "vg_mlkem_sample_ntt" sampleNTT

/-- The indices of the seed: `ρ ‖ j ‖ i` for `Â[i, j]`, with `i` in `r9` and
`j` in `r10`, or `ρ ‖ i ‖ j` for `Â[j, i]` (`transpose`). -/
def seedBytes (transpose : Bool) : List Instr :=
  if transpose then [.strb .r9 .r7 (oSeed + 32), .strb .r10 .r7 (oSeed + 33)]
  else [.strb .r10 .r7 (oSeed + 32), .strb .r9 .r7 (oSeed + 33)]

/-! ## The parameter sets

The top-level functions of ML-KEM-768 and ML-KEM-1024 are the same but for
`k`, `d_u`, `d_v`, the primitives that compress to `d_u` and `d_v` bits, and
the offsets in `scratch` that follow from `k` (`KemLay`).
-/

/-- What the top-level functions of a parameter set need: its parameters
`p` (`k`, `d_u`, `d_v`), the size of `scratch` its contracts give, the shifts
of `c` that sum to `32 d_u · c` (`atU`), and the primitives (and their
symbols) that compress to and decompress from `d_u` and `d_v` bits. -/
structure KemLay where
  p : Spec.MlKem.Params
  scratch : Nat
  uShifts : List Nat
  compressSym : String
  compress : Prog isa
  decompressSym : String
  decompress : Prog isa

namespace KemLay

variable (K : KemLay)

abbrev k : Nat := K.p.k
abbrev du : Nat := K.p.du
abbrev dv : Nat := K.p.dv

/-- The sum of a row (polynomial `3k + 2`), a product (`3k + 3`) and a
sampled entry of `Â` (`3k + 4`). -/
abbrev oAcc : Nat := oPoly (3 * K.k + 2)
abbrev oTmp : Nat := oPoly (3 * K.k + 3)
abbrev oAhat : Nat := oPoly (3 * K.k + 4)
/-- The working space of `vg_mlkem_sample_ntt` (2048 bytes), of the NTTs and
`vg_mlkem_multiply_ntts` (1024 bytes), and the ciphertext `c'` of
decapsulation's re-encryption. -/
abbrev oSample : Nat := oPoly (3 * K.k + 5)
abbrev oNtt : Nat := oPoly (3 * K.k + 7)
abbrev oCt : Nat := oPoly (3 * K.k + 8)

/-- The bytes of `ek`, of `dk`, of `ByteEncode_{d_u}(Compress_{d_u}(u[i]))`, of
`ByteEncode_{d_v}(Compress_{d_v}(v))`, and of the ciphertext. -/
abbrev ekLen : Nat := 384 * K.k + 32
abbrev dkLen : Nat := 768 * K.k + 96
abbrev uLen : Nat := 32 * K.du
abbrev vLen : Nat := 32 * K.dv
abbrev ctLen : Nat := K.uLen * K.k + K.vLen

def callCU : Prog isa := .call K.compressSym K.compress
def callDU : Prog isa := .call K.decompressSym K.decompress

/-- `d ← b + 32 d_u · c`. -/
def atU (d b c : Reg) : List Instr := atShifts d b c K.uShifts

/-! ## Sampling -/

/-- `SamplePolyCBD₂(PRF₂(σ, N))` into polynomial `k + N`, with `N` in `r9`
(and `σ ‖ N` at `920`), then its NTT if `withNtt`. -/
def prfBody (withNtt : Bool) (N₁ : Nat) : Prog isa :=
  .seq (.block [.strb .r9 .r7 (oSigma + 32)]) <|
  .seq (hash 136 0x1f [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩]) <|
  .seq (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly K.k))) <|
  .seq callCbd2 <|
  .seq (if withNtt then .seq (.block (slotAt .r0 .r9 (oPoly K.k) ++ [ptrTo .r1 .r7 K.oNtt])) callNtt
    else .block [])
    (.block (count .r9 N₁))

/-- `prfBody` for `N` from `N₀` to `N₁ - 1`. -/
def prfLoop (withNtt : Bool) (N₀ N₁ : Nat) : Prog isa :=
  .seq (.block [.mov .r9 (.imm (BitVec.ofNat 32 N₀))]) (.loop (K.prfBody withNtt N₁) .ne)

/-- Entry `j` of row `i` (in `r10` and `r9`) of `Â` (or of `Â^⊺`) sampled,
and its product with polynomial `k + j` added to the sum. -/
def rowBody (transpose : Bool) : Prog isa :=
  .seq (.block (seedBytes transpose ++ [ptrTo .r0 .r7 oSeed, ptrTo .r1 .r7 K.oAhat, ptrTo .r2 .r7 K.oSample])) <|
  .seq callSample <|
  .seq (.block [.dp .and .r11 .r11 (.reg .r0), .cmp .r0 (.imm 0)]) <|
  .seq (.ite .eq (.block (slotAt .r1 .r10 (oPoly K.k))) (.block [ptrTo .r1 .r7 K.oAhat])) <|
  .seq (.block (ptrTo .r0 .r7 K.oTmp :: slotAt .r2 .r10 (oPoly K.k) ++ [ptrTo .r3 .r7 K.oNtt])) <|
  .seq callMul <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oTmp]) <|
  .seq callAdd (.block (count .r10 K.k))

/-- Row `i` of `Â ∘ v̂` (or of `Â^⊺ ∘ v̂`), `v̂` polynomials `k` to `2k - 1`,
into polynomial `3k + 2`. -/
def rowSum (transpose : Bool) : Prog isa :=
  .seq (zeroPoly K.oAcc) (.seq (.block [.mov .r10 (.imm 0)]) (.loop (K.rowBody transpose) .ne))

def dotBody : Prog isa :=
  .seq (.block (ptrTo .r0 .r7 K.oTmp :: slotAt .r1 .r10 (oPoly 0) ++ slotAt .r2 .r10 (oPoly K.k) ++
    [ptrTo .r3 .r7 K.oNtt])) <|
  .seq callMul <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oTmp]) <|
  .seq callAdd (.block (count .r10 K.k))

/-- The sum of the products of polynomials `j` and `k + j`, into polynomial
`3k + 2`. -/
def dot : Prog isa := .seq (zeroPoly K.oAcc) (.seq (.block [.mov .r10 (.imm 0)]) (.loop K.dotBody .ne))

end KemLay

/-! ## Saving our caller's registers -/

/-- The return value, and our caller's registers restored. -/
def topEnd : List Instr :=
  [.mov .r0 (.reg .r11), .mov .r3 (.reg .r7)] ++ restoreRegs .r3 oSave ++ ([.ldr .lr .r3 (oSave + 32)] : List Instr)

/-! ## `vg_mlkem<n>_keygen(seed = r0, ek = r1, dk = r2, scratch = r3) -> r0` -/

namespace KemLay

variable (K : KemLay)

def kgSetup : List Instr :=
  saveRegs .r3 oSave ++
    ([.str .lr .r3 (oSave + 32), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r7 (.reg .r3), .mov .r12 (.imm (BitVec.ofNat 32 K.k)), .strb .r12 .r3 oK] : List Instr)

/-- Row `i` (in `r9`) of `t̂ = Â ∘ ŝ + ê`, encoded into `ek`. -/
def kgRowBody : Prog isa :=
  .seq (K.rowSum false) <|
  .seq (.block (ptrTo .r0 .r7 K.oAcc :: slotAt .r1 .r9 (oPoly (2 * K.k)))) <|
  .seq callAdd <|
  .seq (.block (ptrTo .r0 .r7 K.oAcc :: at384 .r1 .r5 .r9)) <|
  .seq callEncode12 (.block (count .r9 K.k))

/-- `ŝ[j]` (`j` in `r9`) encoded into `dk`. -/
def kgSBody : Prog isa :=
  .seq (.block (slotAt .r0 .r9 (oPoly K.k) ++ at384 .r1 .r6 .r9)) (.seq callEncode12 (.block (count .r9 K.k)))

def keygen : Prog isa :=
  .seq (.block K.kgSetup) <|
  .seq (hash 72 0x06 [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (copy .r7 oG .r7 oSeed 32) <|
  .seq (K.prfLoop true 0 (2 * K.k)) <|
  .seq (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) <|
  .seq (.loop K.kgRowBody .ne) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop K.kgSBody .ne) <|
  .seq (copy .r7 oSeed .r5 (384 * K.k) 32) <|
  .seq (copy .r5 0 .r6 (384 * K.k) K.ekLen) <|
  .seq (hash 136 0x06 [⟨.r5, 0, K.ekLen⟩] [⟨.r6, 768 * K.k + 32, 32⟩]) <|
  .seq (copy .r4 32 .r6 (768 * K.k + 64) 32) (.block topEnd)

/-! ## K-PKE.Encrypt, with `ek` in `r4`, `m` in `r5`, `r` at `920` and `c` to `r8` -/

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (`i` in `r9`). -/
def decTBody : Prog isa :=
  .seq (.block (at384 .r0 .r4 .r9 ++ slotAt .r1 .r9 (oPoly 0))) (.seq callDecode12 (.block (count .r9 K.k)))

/-- `u[i]` (`i` in `r9`), compressed and encoded into `c`. -/
def encRowBody : Prog isa :=
  .seq (K.rowSum true) <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oNtt]) <|
  .seq callNttInv <|
  .seq (.block (ptrTo .r0 .r7 K.oAcc :: slotAt .r1 .r9 (oPoly (2 * K.k)))) <|
  .seq callAdd <|
  .seq (.block ([ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.du))] ++ K.atU .r2 .r8 .r9 ++
    [.mov .r3 (.imm (BitVec.ofNat 32 K.uLen))])) <|
  .seq K.callCU (.block (count .r9 K.k))

def encrypt : Prog isa :=
  .seq (copy .r4 (384 * K.k) .r7 oSeed 32) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop K.decTBody .ne) <|
  .seq (K.prfLoop true 0 K.k) <|
  .seq (K.prfLoop false K.k (2 * K.k + 1)) <|
  .seq (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly (3 * K.k + 1))]) <|
  .seq callDecompress <|
  .seq (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) <|
  .seq (.loop K.encRowBody .ne) <|
  .seq K.dot <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oNtt]) <|
  .seq callNttInv <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 (oPoly (3 * K.k))]) <|
  .seq callAdd <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 (oPoly (3 * K.k + 1))]) <|
  .seq callAdd <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r2 .r8 (K.uLen * K.k),
    .mov .r3 (.imm (BitVec.ofNat 32 K.vLen))]) K.callCU

end KemLay

/-! ## `vg_mlkem<n>_encaps(ek = r0, m = r1, key = r2, ct = r3, scratch = [sp]) -> r0` -/

/-- After `scratch` loaded into `r12` from the stack. -/
def encapsSetup : List Instr :=
  saveRegs .r12 oSave ++
    ([.str .lr .r12 (oSave + 32), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r8 (.reg .r3), .mov .r7 (.reg .r12)] : List Instr)

def KemLay.encaps (K : KemLay) : Prog isa :=
  .seq (.block [.ldrSp .r12 0]) <|
  .seq (.block encapsSetup) <|
  .seq (copy .r5 0 .r7 oMsg 32) <|
  .seq (.block [ptrTo .r5 .r7 oMsg]) <|
  .seq (hash 136 0x06 [⟨.r4, 0, K.ekLen⟩] [⟨.r7, oHek, 32⟩]) <|
  .seq (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (copy .r7 oG .r6 0 32) <|
  .seq K.encrypt (.block topEnd)

/-! ## `vg_mlkem<n>_decaps(dk = r0, ct = r1, key = r2, scratch = r3) -> r0` -/

def decapsSetup : List Instr :=
  saveRegs .r3 oSave ++
    ([.str .lr .r3 (oSave + 32), .str .r2 .r3 oExtra, .mov .r4 (.reg .r0), .mov .r6 (.reg .r1),
      .mov .r7 (.reg .r3)] : List Instr)

def cmpBody : List Instr :=
  [.ldrb .r2 .r0 0, .ldrb .r3 .r1 0, .dp .eor .r2 .r2 (.reg .r3), .dp .orr .r12 .r12 (.reg .r2),
   .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1), .subs .r9 .r9 (.imm 1)]

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

namespace KemLay

variable (K : KemLay)

/-- `û[i] = NTT(Decompress_{d_u}(ByteDecode_{d_u}(c[32d_u·i : 32d_u·(i + 1)])))` (`i` in `r9`). -/
def decUBody : Prog isa :=
  .seq (.block (K.atU .r0 .r6 .r9 ++ [.mov .r1 (.imm (BitVec.ofNat 32 K.uLen)), .mov .r2 (.imm (BitVec.ofNat 32 K.du))] ++
    slotAt .r3 .r9 (oPoly K.k))) <|
  .seq K.callDU <|
  .seq (.block (slotAt .r0 .r9 (oPoly K.k) ++ [ptrTo .r1 .r7 K.oNtt])) <|
  .seq callNtt (.block (count .r9 K.k))

/-- K-PKE.Decrypt, with `dk` in `r4` and `c` in `r6`: `m'` to `992`. -/
def decrypt : Prog isa :=
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop K.decUBody .ne) <|
  .seq (.block [.mov .r9 (.imm 0)]) <|
  .seq (.loop K.decTBody .ne) <|
  .seq K.dot <|
  .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oNtt]) <|
  .seq callNttInv <|
  .seq (.block [ptrTo .r0 .r6 (K.uLen * K.k), .mov .r1 (.imm (BitVec.ofNat 32 K.vLen)),
    .mov .r2 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r3 .r7 (oPoly (3 * K.k))]) <|
  .seq K.callDU <|
  .seq (.block [ptrTo .r0 .r7 (oPoly (3 * K.k)), ptrTo .r1 .r7 K.oAcc]) <|
  .seq callSub <|
  .seq (.block [ptrTo .r0 .r7 (oPoly (3 * K.k)), .mov .r1 (.imm 1), ptrTo .r2 .r7 oMsg, .mov .r3 (.imm 32)])
    callCompress

/-- The OR of the XORs of the bytes of `c` (`r6`) and `c'`, into `r12`. -/
def compare : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r6), ptrTo .r1 .r7 K.oCt, .mov .r12 (.imm 0),
    .mov .r9 (.imm (BitVec.ofNat 32 K.ctLen))])
    (.loop (.block cmpBody) .ne)

def decaps : Prog isa :=
  .seq (.block decapsSetup) <|
  .seq (copy .r6 0 .r7 oCin K.ctLen) <|
  .seq (.block [ptrTo .r6 .r7 oCin]) <|
  .seq K.decrypt <|
  .seq (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r4, 768 * K.k + 32, 32⟩] [⟨.r7, oG, 64⟩]) <|
  .seq (hash 136 0x1f [⟨.r4, 768 * K.k + 64, 32⟩, ⟨.r7, oCin, K.ctLen⟩] [⟨.r7, oKbar, 32⟩]) <|
  .seq (.block [ptrTo .r4 .r4 (384 * K.k), ptrTo .r5 .r7 oMsg, ptrTo .r8 .r7 K.oCt]) <|
  .seq K.encrypt <|
  .seq K.compare <|
  .seq (.block selSetup) <|
  .seq (.loop (.block selBody) .ne) (.block topEnd)

end KemLay

/-! ## ML-KEM-768

`k = 3`, `d_u = 10`, `d_v = 4`: `scratch` holds polynomials `0` to `13`
below 16384, and `c'` at 19456. -/

/-- ML-KEM-768's parameters, which compress with `vg_mlkem_compress_encode`. -/
def kl768 : KemLay :=
  ⟨Spec.MlKem.mlKem768, 32768, [8, 6], "vg_mlkem_compress_encode", compressEncode, "vg_mlkem_decode_decompress",
    decodeDecompress⟩

abbrev keygen : Prog isa := kl768.keygen
abbrev encaps : Prog isa := kl768.encaps
abbrev decaps : Prog isa := kl768.decaps

end VG.Impl.MlKem.Arm

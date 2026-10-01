import VerifiedGarbage.TCB.X86_64.Avx

/-!
# x86-64 AVX-512 instructions

**Trusted.** The EVEX-encoded (AVX-512F) instructions of the x86-64 model in
`TCB/X86_64/Isa.lean` that write only vector registers, all with 512-bit
(`zmm`) operands and no masking, and the operations of those with an
embedded-broadcast memory operand (`ZBcstOp`, which `Isa.lean` runs since
they read memory).
-/

namespace VG.X86_64

/-- EVEX-encoded three-operand instructions `vop zmm, zmm, zmm` that act on
each 128-bit lane as the legacy SSE instruction does on its destination
(`src1`) and source (`src2`). -/
inductive ZBinOp
  | vpaddd | vpxord | vpunpckldq | vpunpckhdq | vpunpcklqdq | vpunpckhqdq
  deriving DecidableEq, Repr

/-- AVX-512 instructions with 512-bit operands that write only vector
registers. None is masked: the opmask is `k0` (`EVEX.aaa = 000`), so every
element of the destination is written. -/
inductive ZOp
  /-- `vop zmm1, zmm2, zmm3` -/
  | zbin (op : ZBinOp) (dst src1 src2 : XReg)
  /-- `vprold zmm1, zmm2, imm8` (`EVEX.512.66.0F.W0 72 /1 ib`) -/
  | vprold (dst src : XReg) (count : BitVec 8)
  /-- `vpshufd zmm1, zmm2, imm8` (`EVEX.512.66.0F.W0 70 /r ib`) -/
  | vpshufd (dst src : XReg) (order : BitVec 8)
  /-- `vshufi32x4 zmm1, zmm2, zmm3, imm8` (`EVEX.512.66.0F3A.W0 43 /r ib`) -/
  | vshufi32x4 (dst src1 src2 : XReg) (sel : BitVec 8)
  deriving DecidableEq, Repr

/-- The legacy SSE instruction whose operation `op` applies to each lane:
VPADDD, VPXORD and VPUNPCK{L,H}{DQ,QDQ} are, lane by lane, PADDD, PXOR and
PUNPCK{L,H}{DQ,QDQ} (SDM Vol. 2, each instruction's "EVEX.512 encoded
version" pseudocode, with `SRC1` in place of the destination and no write
mask: VPADDD and VPXORD act on each doubleword, and VPUNPCK* interleave the
elements of each 128-bit lane as the VEX.256 forms do on two). -/
def ZBinOp.sse : ZBinOp → XBinOp
  | .vpaddd => .paddd | .vpxord => .pxor
  | .vpunpckldq => .punpckldq | .vpunpckhdq => .punpckhdq
  | .vpunpcklqdq => .punpcklqdq | .vpunpckhqdq => .punpckhqdq

/-- EVEX-encoded three-operand instructions `vop zmm, zmm, m64bcst` whose
second source is a quadword in memory broadcast to every element
(`QWORD PTR [m]{1to8}`, `EVEX.b = 1`); see `ZBcstOp.sse`. -/
inductive ZBcstOp
  | vpmuludq | vpandq | vporq
  deriving DecidableEq, Repr

/-- The legacy SSE instruction whose operation `op` applies to each lane,
with the loaded quadword in both quadwords of its source. SDM Vol. 2, each
instruction's "EVEX encoded versions" pseudocode with `(KL, VL) = (8, 512)`,
no write mask and a memory `SRC2` with `EVEX.b = 1`, for each quadword
`j` from 0 to 7 (`i := j * 64`):

* VPMULUDQ ("PMULUDQ"): `IF (EVEX.b = 1) AND (SRC2 *is memory*) THEN
  DEST[i+63:i] := ZeroExtend64( SRC1[i+31:i]) * ZeroExtend64( SRC2[31:0] )`.
* VPANDQ ("PAND"): `IF (EVEX.b = 1) AND (SRC2 *is memory*) THEN
  DEST[i+63:i] := SRC1[i+63:i] BITWISE AND SRC2[63:0]`.
* VPORQ ("POR/VPOR/VPORD/VPORQ"): the SDM gives the pseudocode of VPORD
  only, `IF (EVEX.b = 1) AND (SRC2 *is memory*) THEN DEST[i+31:i] :=
  SRC1[i+31:i] BITWISE OR SRC2[31:0]` for each doubleword (`i := j * 32`),
  and describes VPORQ as the same on quadwords, its source "a 512/256/128-bit
  vector broadcasted from a 32/64-bit memory location" (the 64-bit one for
  VPORQ): `DEST[i+63:i] := SRC1[i+63:i] BITWISE OR SRC2[63:0]` with
  `i := j * 64`, as VPANDQ.

Each quadword of `DEST` is that of `SRC1` combined with `SRC2[63:0]`, so
on each 128-bit lane this is PMULUDQ, PAND and POR (`XBinOp.eval`) of the
lane of `SRC1` and `SRC2[63:0]` twice: PMULUDQ multiplies the low
doubleword of each quadword, and the low doubleword of `SRC2[63:0]` is
`SRC2[31:0]`. -/
def ZBcstOp.sse : ZBcstOp → XBinOp
  | .vpmuludq => .pmuludq | .vpandq => .pand | .vporq => .por

/-- SDM Vol. 2, "VPROLD/VPROLVD/VPROLQ/VPROLVQ", for one lane:
`LEFT_ROTATE_DWORDS(SRC, COUNT_SRC) { COUNT := COUNT_SRC modulo 32;
DEST[31:0] := (SRC << COUNT) | (SRC >> (32 - COUNT)); }` for each
doubleword. -/
def rolDwords (x : BitVec 128) (n : BitVec 8) : BitVec 128 :=
  let r (i : Nat) := (dword x i).rotateLeft (n.toNat % 32)
  ofDwords (r 0) (r 1) (r 2) (r 3)

/-- SDM Vol. 2, "VSHUFF32x4/VSHUFF64x2/VSHUFI32x4/VSHUFI64x2", 512-bit form:
`Select4(SRC, control) { CASE (control[1:0]) OF 0: TMP := SRC[127:0]; 1:
TMP := SRC[255:128]; 2: TMP := SRC[383:256]; 3: TMP := SRC[511:384]; }`,
`DEST[127:0] := Select4(SRC1, imm8[1:0]); DEST[255:128] := Select4(SRC1,
imm8[3:2]); DEST[383:256] := Select4(SRC2, imm8[5:4]); DEST[511:384] :=
Select4(SRC2, imm8[7:6])`. Here `a i` and `b i` are lane `i` of `SRC1` and
`SRC2`, and the result is lane `j` of `DEST`. -/
def shuf4Lanes (a b : Nat → BitVec 128) (sel : BitVec 8) (j : Nat) : BitVec 128 :=
  let k := (sel.extractLsb' (2 * j) 2).toNat
  if j < 2 then a k else b k

/-- Semantics of an AVX-512 instruction that writes only vector registers.
SDM Vol. 2 (no flags are affected; with 512-bit operands the whole of
`DEST[511:0]` is written):

* The lane-wise instructions: see `ZBinOp.sse`, `rolDwords` (VPROLD) and
  `shufDwords` (VPSHUFD: "EVEX.512 encoded version", each lane with the
  same `imm8`).
* VSHUFI32X4: see `shuf4Lanes`. -/
def ZOp.exec : ZOp → State → State
  | .zbin op d a b, s =>
    let f (i : Nat) := op.sse.eval (s.zlane a i) (s.zlane b i)
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vprold d r n, s =>
    let f (i : Nat) := rolDwords (s.zlane r i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpshufd d r o, s =>
    let f (i : Nat) := shufDwords (s.zlane r i) o
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vshufi32x4 d a b n, s =>
    let f := shuf4Lanes (s.zlane a) (s.zlane b) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)

end VG.X86_64

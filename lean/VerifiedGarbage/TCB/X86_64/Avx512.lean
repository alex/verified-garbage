import VerifiedGarbage.TCB.X86_64.Avx

/-!
# x86-64 AVX-512 instructions

**Trusted.** The EVEX-encoded (AVX-512F) instructions of the x86-64 model in
`TCB/X86_64/Isa.lean` that write only vector registers, all with 512-bit
(`zmm`) operands and no masking.
-/

namespace VG.X86_64

/-- EVEX-encoded three-operand instructions `vop zmm, zmm, zmm` that act on
each 128-bit lane as the legacy SSE instruction does on its destination
(`src1`) and source (`src2`). -/
inductive ZBinOp
  | vpaddd | vpxord | vpunpckldq | vpunpckhdq | vpunpcklqdq | vpunpckhqdq
  | vpaddq | vpmuludq | vpandq | vporq | vpandnq
  deriving DecidableEq, Repr

/-- EVEX-encoded shifts of each quadword by an immediate count,
`vop zmm1, zmm2, imm8`. -/
inductive ZShiftOp | vpsllq | vpsrlq
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
  /-- `vpsllq zmm1, zmm2, imm8` (`EVEX.512.66.0F.W1 73 /6 ib`) or `vpsrlq zmm1,
  zmm2, imm8` (`EVEX.512.66.0F.W1 73 /2 ib`) -/
  | vshift (op : ZShiftOp) (dst src : XReg) (count : BitVec 8)
  /-- `vpbroadcastq zmm1, xmm2` (`EVEX.512.66.0F38.W1 59 /r`) -/
  | vpbroadcastq (dst src : XReg)
  /-- `vmovdqa64 zmm1, zmm2` (`EVEX.512.66.0F.W1 6F /r`) -/
  | vmovdqa64 (dst src : XReg)
  deriving DecidableEq, Repr

/-- The legacy SSE instruction whose operation `op` applies to each lane:
VPADDD, VPXORD, VPUNPCK{L,H}{DQ,QDQ}, VPADDQ, VPMULUDQ, VPANDQ, VPORQ and
VPANDNQ are, lane by lane, PADDD, PXOR, PUNPCK{L,H}{DQ,QDQ}, PADDQ, PMULUDQ,
PAND, POR and PANDN (SDM Vol. 2, each instruction's "EVEX.512 encoded
version" pseudocode, with `SRC1` in place of the destination and no write
mask nor embedded broadcast, the second source being a register: VPADDD and
VPXORD act on each doubleword; VPADDQ (`DEST[i+63:i] := SRC1[i+63:i] +
SRC2[i+63:i]`), VPANDQ, VPORQ and VPANDNQ (`DEST[i+63:i] := ((NOT
SRC1[i+63:i]) BITWISE AND SRC2[i+63:i])`) on each quadword, which on each
128-bit lane is what PADDQ, PAND, POR and PANDN compute; VPMULUDQ
(`DEST[i+63:i] := ZeroExtend64( SRC1[i+31:i]) * ZeroExtend64( SRC2[i+31:i]
)`) multiplies the low doublewords of each quadword, as PMULUDQ does on
each lane's two; and VPUNPCK* interleave the elements of each 128-bit lane
as the VEX.256 forms do on two). -/
def ZBinOp.sse : ZBinOp → XBinOp
  | .vpaddd => .paddd | .vpxord => .pxor
  | .vpunpckldq => .punpckldq | .vpunpckhdq => .punpckhdq
  | .vpunpcklqdq => .punpcklqdq | .vpunpckhqdq => .punpckhqdq
  | .vpaddq => .paddq | .vpmuludq => .pmuludq | .vpandq => .pand | .vporq => .por
  | .vpandnq => .pandn

/-- The legacy SSE shift whose operation `op` applies to each lane: SDM Vol.
2, "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", "VPSLLQ (EVEX versions,
imm8)": `DEST[i+63:i] := LOGICAL_LEFT_SHIFT_QWORDS(SRC1[i+63:i], imm8)` for
each quadword (no write mask, a register source), and VPSRLQ likewise with
`LOGICAL_RIGHT_SHIFT_QWORDS`: on each 128-bit lane what PSLLQ and PSRLQ
compute (a count above 63 gives zero). -/
def ZShiftOp.sse : ZShiftOp → XShiftOp
  | .vpsllq => .psllq | .vpsrlq => .psrlq

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
* VSHUFI32X4: see `shuf4Lanes`.
* VPSLLQ and VPSRLQ: see `ZShiftOp.sse`.
* VPBROADCASTQ (EVEX.512 encoded version, register source, no write mask):
  every quadword of `DEST` is `SRC[63:0]`.
* VMOVDQA64 (EVEX.512 encoded version, register to register, no write
  mask): `DEST[511:0] := SRC[511:0]`. -/
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
  | .vshift op d r n, s =>
    let f (i : Nat) := op.sse.eval (s.zlane r i) n
    s.setZ d (f 0) (f 1) (f 2) (f 3)
  | .vpbroadcastq d r, s =>
    let x := qword (s.xmm r) 0 ++ qword (s.xmm r) 0
    s.setZ d x x x x
  | .vmovdqa64 d r, s => s.setZ d (s.zlane r 0) (s.zlane r 1) (s.zlane r 2) (s.zlane r 3)

end VG.X86_64

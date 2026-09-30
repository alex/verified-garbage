import VerifiedGarbage.TCB.X86_64.Sse

/-!
# x86-64 AVX instructions

**Trusted.** The VEX-encoded (AVX and AVX2) instructions of the x86-64 model
in `TCB/X86_64/Isa.lean` that write only vector registers.
-/

namespace VG.X86_64

/-- VEX-encoded three-operand instructions `vop dst, src1, src2` that act on
each 128-bit lane as the legacy SSE instruction does on its destination
(`src1`) and source (`src2`). -/
inductive VBinOp
  | vpaddd | vpaddq | vpxor | vpor | vpand | vpandn | vpshufb | vpmuludq
  | vpunpckldq | vpunpckhdq | vpunpcklqdq | vpunpckhqdq
  | vpaddw | vpsubw | vpsubd | vpmullw | vpmulhw | vpackssdw | vpunpcklwd | vpunpckhwd
  deriving DecidableEq, Repr

/-- AVX2 shifts of each element by the count in the corresponding element
of a register. -/
inductive VVarOp | vpsllvd | vpsrlvd | vpsllvq | vpsrlvq
  deriving DecidableEq, Repr

/-- AVX instructions that write only vector registers. -/
inductive VOp
  /-- `vop dst, src1, src2` -/
  | vbin (op : VBinOp) (len : VLen) (dst src1 src2 : XReg)
  /-- `vmovdqa dst, src` -/
  | vmovdqa (len : VLen) (dst src : XReg)
  /-- `vop dst, src, imm8` (`vpslld`, `vpsrld`, `vpsllq`, `vpsrlq`, `vpslldq`,
  `vpsrldq`) -/
  | vshift (op : XShiftOp) (len : VLen) (dst src : XReg) (count : BitVec 8)
  /-- `vpshufd dst, src, imm8` -/
  | vpshufd (len : VLen) (dst src : XReg) (order : BitVec 8)
  /-- `vpalignr dst, src1, src2, imm8` -/
  | vpalignr (len : VLen) (dst src1 src2 : XReg) (shift : BitVec 8)
  /-- `vpblendd dst, src1, src2, imm8` -/
  | vpblendd (len : VLen) (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vop dst, src1, src2` (`vpsllvd`, `vpsrlvd`, `vpsllvq`, `vpsrlvq`) -/
  | vvar (op : VVarOp) (len : VLen) (dst src1 src2 : XReg)
  /-- `vpbroadcastd dst, xmm` -/
  | vpbroadcastd (len : VLen) (dst src : XReg)
  /-- `vpbroadcastq dst, xmm` -/
  | vpbroadcastq (len : VLen) (dst src : XReg)
  /-- `vpermq ymm1, ymm2, imm8` -/
  | vpermq (dst src : XReg) (order : BitVec 8)
  /-- `vperm2i128 ymm1, ymm2, ymm3, imm8` -/
  | vperm2i128 (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vinserti128 ymm1, ymm2, xmm3, imm8` -/
  | vinserti128 (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vextracti128 xmm1, ymm2, imm8` -/
  | vextracti128 (dst src : XReg) (sel : BitVec 8)
  /-- `vmovq xmm, r64` (`VEX.128.66.0F.W1 6E /r`) -/
  | vmovq (dst : XReg) (src : Reg)
  /-- `vzeroupper` -/
  | vzeroupper
  /-- `vsha512rnds2 ymm1, ymm2, xmm3` (`VEX.256.F2.0F38.W0 CB /r`, SHA512):
  two SHA-512 rounds, with `C, D, G, H` in `ymm1` (`dst`), `A, B, E, F` in
  `ymm2` (`src1`) and `Wₜ + Kₜ` for the two rounds in `xmm3` (`src2`). -/
  | vsha512rnds2 (dst src1 src2 : XReg)
  /-- `vsha512msg1 ymm1, xmm2` (`VEX.256.F2.0F38.W0 CC /r`, SHA512): the
  `σ₀` part of the next four message words. -/
  | vsha512msg1 (dst src : XReg)
  /-- `vsha512msg2 ymm1, ymm2` (`VEX.256.F2.0F38.W0 CD /r`, SHA512): the
  `σ₁` part of the next four message words. -/
  | vsha512msg2 (dst src : XReg)
  deriving DecidableEq, Repr

/-! ### AVX

The SDM defines most VEX-encoded integer instructions on 256-bit operands as
the 128-bit operation applied to each 128-bit lane (e.g. "VPADDD (VEX.256
encoded version)": the doubleword sums of `SRC1[127:0]` and `SRC2[127:0]`
into `DEST[127:0]`, then of `SRC1[255:128]` and `SRC2[255:128]` into
`DEST[255:128]`); `VEX.128` versions compute lane 0 only and zero the rest. -/

/-- The legacy SSE instruction whose operation `op` applies to each lane:
VPADDD, VPADDQ, VPXOR, VPOR, VPAND, VPANDN, VPSHUFB, VPMULUDQ,
VPUNPCK{L,H}{DQ,QDQ}, VPADDW, VPSUBW, VPSUBD, VPMULLW, VPMULHW, VPACKSSDW
and VPUNPCK{L,H}WD are, lane by lane, PADDD, PADDQ, PXOR, POR, PAND, PANDN,
PSHUFB, PMULUDQ, PUNPCK{L,H}{DQ,QDQ}, PADDW, PSUBW, PSUBD, PMULLW, PMULHW,
PACKSSDW and PUNPCK{L,H}WD (SDM Vol. 2, each instruction's "VEX.256 encoded
version" pseudocode, with `SRC1` in place of the destination; VPACKSSDW
and VPUNPCK{L,H}WD pack and interleave within each 128-bit lane). -/
def VBinOp.sse : VBinOp → XBinOp
  | .vpaddd => .paddd | .vpaddq => .paddq | .vpxor => .pxor | .vpor => .por
  | .vpand => .pand | .vpandn => .pandn | .vpshufb => .pshufb | .vpmuludq => .pmuludq
  | .vpunpckldq => .punpckldq | .vpunpckhdq => .punpckhdq
  | .vpunpcklqdq => .punpcklqdq | .vpunpckhqdq => .punpckhqdq
  | .vpaddw => .paddw | .vpsubw => .psubw | .vpsubd => .psubd | .vpmullw => .pmullw
  | .vpmulhw => .pmulhw | .vpackssdw => .packssdw | .vpunpcklwd => .punpcklwd
  | .vpunpckhwd => .punpckhwd

/-- SDM Vol. 2, "VPBLENDD", for one lane (`imm` holding that lane's four
selector bits): `IF (imm8[i]) THEN DEST[32i+31:32i] := SRC2[32i+31:32i]
ELSE DEST[32i+31:32i] := SRC1[32i+31:32i]`. -/
def blendDwords (a b : BitVec 128) (imm : BitVec 4) : BitVec 128 :=
  let pick (i : Nat) : BitVec 32 := if imm.getLsbD i then dword b i else dword a i
  ofDwords (pick 0) (pick 1) (pick 2) (pick 3)

/-- SDM Vol. 2, "VPSLLVD/VPSLLVQ" and "VPSRLVD/VPSRLVQ", for one lane:
`COUNT := SRC2[32i+31:32i]; IF COUNT < 32 THEN DEST[32i+31:32i] :=
ZeroExtend(SRC1[32i+31:32i] << COUNT) ELSE DEST[32i+31:32i] := 0`
(respectively `>>`, a logical shift) for each doubleword `i`, and likewise
for quadwords with `COUNT < 64`. -/
def VVarOp.eval (op : VVarOp) (a b : BitVec 128) : BitVec 128 :=
  let dwords (f : BitVec 32 → Nat → BitVec 32) : BitVec 128 :=
    let e (i : Nat) := let n := (dword b i).toNat; if n < 32 then f (dword a i) n else 0
    ofDwords (e 0) (e 1) (e 2) (e 3)
  let qwords (f : BitVec 64 → Nat → BitVec 64) : BitVec 128 :=
    let e (i : Nat) := let n := (qword b i).toNat; if n < 64 then f (qword a i) n else 0
    e 1 ++ e 0
  match op with
  | .vpsllvd => dwords (· <<< ·)
  | .vpsrlvd => dwords (· >>> ·)
  | .vpsllvq => qwords (· <<< ·)
  | .vpsrlvq => qwords (· >>> ·)

/-- Quadword `i` (bits `64i+63:64i`) of a 256-bit value. -/
def qword256 (x : BitVec 256) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-! ### SHA512

SDM Vol. 2, "VSHA512MSG1", "VSHA512MSG2" and "VSHA512RNDS2" (the SHA512
extension): the functions of FIPS 180-4 §4.1.3 on quadwords, as the SDM's
pseudocode defines them (`ROR64(qword, n) := (qword >> n) | (qword << (64 -
n))`, `SHR64(qword, n) := qword >> n`). -/

def sha512Ch (x y z : BitVec 64) : BitVec 64 := (x &&& y) ^^^ (z &&& ~~~x)

def sha512Maj (x y z : BitVec 64) : BitVec 64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `cap_sigma0` -/
def sha512BigSigma0 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39

/-- `cap_sigma1` -/
def sha512BigSigma1 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41

/-- `s0` -/
def sha512Sigma0 (x : BitVec 64) : BitVec 64 := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> 7

/-- `s1` -/
def sha512Sigma1 (x : BitVec 64) : BitVec 64 := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> 6

/-- VSHA512MSG1: `W[4] := SRC.qword[0]; W[3] := DEST.qword[3]; W[2] :=
DEST.qword[2]; W[1] := DEST.qword[1]; W[0] := DEST.qword[0];
DEST.qword[3] := W[3] + s0(W[4]); DEST.qword[2] := W[2] + s0(W[3]);
DEST.qword[1] := W[1] + s0(W[2]); DEST.qword[0] := W[0] + s0(W[1])`. -/
def sha512Msg1 (dst : BitVec 256) (src : BitVec 128) : BitVec 256 :=
  let w (i : Nat) := qword256 dst i
  (w 3 + sha512Sigma0 (src.extractLsb' 0 64)) ++ (w 2 + sha512Sigma0 (w 3)) ++
    (w 1 + sha512Sigma0 (w 2)) ++ (w 0 + sha512Sigma0 (w 1))

/-- VSHA512MSG2: `W[14] := SRC.qword[2]; W[15] := SRC.qword[3]; W[16] :=
DEST.qword[0] + s1(W[14]); W[17] := DEST.qword[1] + s1(W[15]); W[18] :=
DEST.qword[2] + s1(W[16]); W[19] := DEST.qword[3] + s1(W[17]);
DEST.qword[3] := W[19]; DEST.qword[2] := W[18]; DEST.qword[1] := W[17];
DEST.qword[0] := W[16]`. -/
def sha512Msg2 (dst src : BitVec 256) : BitVec 256 :=
  let w16 := qword256 dst 0 + sha512Sigma1 (qword256 src 2)
  let w17 := qword256 dst 1 + sha512Sigma1 (qword256 src 3)
  let w18 := qword256 dst 2 + sha512Sigma1 w16
  let w19 := qword256 dst 3 + sha512Sigma1 w17
  w19 ++ w18 ++ w17 ++ w16

/-- VSHA512RNDS2: `A[0] := SRC1.qword[3]; B[0] := SRC1.qword[2]; C[0] :=
DEST.qword[3]; D[0] := DEST.qword[2]; E[0] := SRC1.qword[1]; F[0] :=
SRC1.qword[0]; G[0] := DEST.qword[1]; H[0] := DEST.qword[0]; WK[0] :=
SRC2.qword[0]; WK[1] := SRC2.qword[1]; FOR i := 0 to 1: A[i+1] :=
CH(E[i], F[i], G[i]) + cap_sigma1(E[i]) + WK[i] + H[i] + MAJ(A[i], B[i],
C[i]) + cap_sigma0(A[i]); B[i+1] := A[i]; C[i+1] := B[i]; D[i+1] := C[i];
E[i+1] := CH(E[i], F[i], G[i]) + cap_sigma1(E[i]) + WK[i] + H[i] + D[i];
F[i+1] := E[i]; G[i+1] := F[i]; H[i+1] := G[i]; ENDFOR; DEST.qword[3] :=
A[2]; DEST.qword[2] := B[2]; DEST.qword[1] := E[2]; DEST.qword[0] :=
F[2]`. -/
def sha512Rnds2 (dst src1 : BitVec 256) (src2 : BitVec 128) : BitVec 256 :=
  let a0 := qword256 src1 3
  let b0 := qword256 src1 2
  let c0 := qword256 dst 3
  let d0 := qword256 dst 2
  let e0 := qword256 src1 1
  let f0 := qword256 src1 0
  let g0 := qword256 dst 1
  let h0 := qword256 dst 0
  let wk0 := src2.extractLsb' 0 64
  let wk1 := src2.extractLsb' 64 64
  let a1 := sha512Ch e0 f0 g0 + sha512BigSigma1 e0 + wk0 + h0 + sha512Maj a0 b0 c0 +
    sha512BigSigma0 a0
  let b1 := a0
  let c1 := b0
  let d1 := c0
  let e1 := sha512Ch e0 f0 g0 + sha512BigSigma1 e0 + wk0 + h0 + d0
  let f1 := e0
  let g1 := f0
  let h1 := g0
  let a2 := sha512Ch e1 f1 g1 + sha512BigSigma1 e1 + wk1 + h1 + sha512Maj a1 b1 c1 +
    sha512BigSigma0 a1
  let b2 := a1
  let e2 := sha512Ch e1 f1 g1 + sha512BigSigma1 e1 + wk1 + h1 + d1
  let f2 := e1
  a2 ++ b2 ++ e2 ++ f2

/-- SDM Vol. 2, "VPERMQ" (immediate form): `DEST[63:0] := (SRC >>
(IMM8[1:0] * 64))[63:0]; DEST[127:64] := (SRC >> (IMM8[3:2] * 64))[63:0];
DEST[191:128] := (SRC >> (IMM8[5:4] * 64))[63:0]; DEST[255:192] := (SRC >>
(IMM8[7:6] * 64))[63:0]`. -/
def permQwords (x : BitVec 256) (order : BitVec 8) : BitVec 256 :=
  let q (i : Nat) := qword256 x (order.extractLsb' (2 * i) 2).toNat
  q 3 ++ q 2 ++ q 1 ++ q 0

/-- SDM Vol. 2, "VPERM2I128": `CASE IMM8[1:0] of 0: DEST[127:0] :=
SRC1[127:0]; 1: DEST[127:0] := SRC1[255:128]; 2: DEST[127:0] :=
SRC2[127:0]; 3: DEST[127:0] := SRC2[255:128]`, likewise `IMM8[5:4]` for
`DEST[255:128]`; `IF (imm8[3]) DEST[127:0] := 0; IF (imm8[7])
DEST[255:128] := 0`. Here `a i` and `b i` are lane `i` of `SRC1` and
`SRC2`, and the result is lane `j` of `DEST`. -/
def perm2Lanes (a b : Nat → BitVec 128) (sel : BitVec 8) (j : Nat) : BitVec 128 :=
  if sel.getLsbD (4 * j + 3) then 0 else
    let k := (sel.extractLsb' (4 * j) 2).toNat
    if k < 2 then a (k % 2) else b (k % 2)

/-- Semantics of an AVX instruction that writes only vector registers. SDM
Vol. 2 (no flags are affected; `VEX.128` versions zero `DEST[MAXVL-1:128]`):

* The lane-wise instructions: see `VBinOp.sse`, `XShiftOp.eval` (VPSLLW,
  VPSRLW, VPSRAW, VPSLLD, VPSRLD, VPSRAD, VPSLLQ, VPSRLQ, VPSLLDQ and
  VPSRLDQ with an immediate count, each lane as the legacy SSE form on
  `SRC`), `shufDwords` (VPSHUFD, each lane
  with the same `imm8`), `alignRight` (VPALIGNR: `temp1[255:0] :=
  ((SRC1[127:0] << 128) OR SRC2[127:0]) >> (imm8*8)`, and likewise for
  bits 255:128), `blendDwords` (VPBLENDD, lane `j` selected by
  `imm8[4j+3:4j]`), and `VVarOp.eval`.
* VMOVDQA (register form): `DEST[255:0] := SRC[255:0]` (`VEX.128`:
  `DEST[127:0] := SRC[127:0]`).
* VPBROADCASTD/VPBROADCASTQ (register source): every doubleword
  (quadword) of `DEST` is `SRC[31:0]` (`SRC[63:0]`).
* VPERMQ: see `permQwords`. VPERM2I128: see `perm2Lanes`.
* VINSERTI128: `TEMP[255:0] := SRC1[255:0]; CASE (imm8[0]) OF 0:
  TEMP[127:0] := SRC2[127:0]; 1: TEMP[255:128] := SRC2[127:0]; DEST :=
  TEMP`.
* VEXTRACTI128 (register destination): `CASE (imm8[0]) OF 0: DEST[127:0]
  := SRC1[127:0]; 1: DEST[127:0] := SRC1[255:128]; DEST[MAXVL-1:128] := 0`.
* VMOVQ xmm, r64: `DEST[63:0] := SRC[63:0]; DEST[MAXVL-1:64] := 0`.
* VZEROUPPER: in 64-bit mode, `YMM0[MAXVL-1:128] := 0` … `YMM15[MAXVL-1:128]
  := 0` (bits 255:128 and 511:256 of each).
* VSHA512RNDS2, VSHA512MSG1 and VSHA512MSG2: see `sha512Rnds2`,
  `sha512Msg1` and `sha512Msg2` (`DEST[MAXVL-1:256] := 0`). -/
def VOp.exec : VOp → State → State
  | .vbin op len d a b, s =>
    s.setV len d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1))
  | .vmovdqa len d r, s => s.setV len d (s.lane r 0) (s.lane r 1)
  | .vshift op len d r n, s => s.setV len d (op.eval (s.lane r 0) n) (op.eval (s.lane r 1) n)
  | .vpshufd len d r o, s => s.setV len d (shufDwords (s.lane r 0) o) (shufDwords (s.lane r 1) o)
  | .vpalignr len d a b n, s =>
    s.setV len d (alignRight (s.lane a 0) (s.lane b 0) n) (alignRight (s.lane a 1) (s.lane b 1) n)
  | .vpblendd len d a b n, s =>
    s.setV len d (blendDwords (s.lane a 0) (s.lane b 0) (n.extractLsb' 0 4))
      (blendDwords (s.lane a 1) (s.lane b 1) (n.extractLsb' 4 4))
  | .vvar op len d a b, s =>
    s.setV len d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1))
  | .vpbroadcastd len d r, s =>
    let v := dword (s.xmm r) 0
    let x := ofDwords v v v v
    s.setV len d x x
  | .vpbroadcastq len d r, s =>
    let x := qword (s.xmm r) 0 ++ qword (s.xmm r) 0
    s.setV len d x x
  | .vpermq d r o, s =>
    let x := permQwords (s.ymm r) o
    s.setV .l256 d (x.extractLsb' 0 128) (x.extractLsb' 128 128)
  | .vperm2i128 d a b n, s =>
    s.setV .l256 d (perm2Lanes (s.lane a) (s.lane b) n 0) (perm2Lanes (s.lane a) (s.lane b) n 1)
  | .vinserti128 d a b n, s =>
    if n.getLsbD 0 then s.setV .l256 d (s.lane a 0) (s.xmm b)
    else s.setV .l256 d (s.xmm b) (s.lane a 1)
  | .vextracti128 d r n, s => s.setV .l128 d (s.lane r (if n.getLsbD 0 then 1 else 0)) 0
  | .vmovq d r, s => s.setV .l128 d ((0 : BitVec 64) ++ s.gpr r) 0
  | .vzeroupper, s => { s with ymmHi := fun _ => 0, zmmHi := fun _ => 0 }
  | .vsha512rnds2 d a b, s =>
    let x := sha512Rnds2 (s.ymm d) (s.ymm a) (s.xmm b)
    s.setV .l256 d (x.extractLsb' 0 128) (x.extractLsb' 128 128)
  | .vsha512msg1 d r, s =>
    let x := sha512Msg1 (s.ymm d) (s.xmm r)
    s.setV .l256 d (x.extractLsb' 0 128) (x.extractLsb' 128 128)
  | .vsha512msg2 d r, s =>
    let x := sha512Msg2 (s.ymm d) (s.ymm r)
    s.setV .l256 d (x.extractLsb' 0 128) (x.extractLsb' 128 128)

end VG.X86_64

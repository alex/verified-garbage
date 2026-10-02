import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
import VerifiedGarbage.Impl.MlKem.X86_64.Avx
import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Avx2

/-!
# ML-DSA on x86-64: the polynomial arithmetic with AVX2

`vg_mldsa_ntt_avx2`, `vg_mldsa_inv_ntt_avx2`, `vg_mldsa_multiply_ntt_avx2`,
`vg_mldsa_multiply_add_ntt_avx2`, `vg_mldsa_add_avx2` and
`vg_mldsa_sub_avx2` are their SSE2 versions (`Ntt.lean`, `Mul.lean`,
`AddSub.lean`) on eight coefficients at a time, four in each 128-bit lane of
AVX2 registers: in each lane, the VEX.256 form of the SSE2 code (`toY`,
`Impl/MlKem/X86_64/Avx.lean`) does what the SSE2 code does to an `xmm`
register, with `q`, `-q⁻¹ mod 2³²` (and `2⁶⁴ mod q`) in both lanes of
`ymm15`, `ymm14` (and `ymm11`) (`yconsts`).

The layers of the NTT and its inverse, each a pass over `f` with `rdx` at
the coefficients it loads and `r8` at the zetas of the table:

* `len ≥ 8` (`ylay`): each block with its zeta in both lanes of `ymm13`
  (`yzeta1`), and `len / 8` times the butterflies of the eight
  coefficients `w[j]` and the eight `w[j + len]`;
* `len = 4` (`ylay4`): two blocks at a time, their lower halves gathered
  into `ymm0` and their upper halves into `ymm1` by `vperm2i128`, with the
  zeta of each in a lane of `ymm13` (`yzetaS`: `vpshufd` and `vpblendd`);
* `len = 2` and `len = 1` (`ylay2`, `ylay1`): in each lane `l`, what
  `vlay2` and `vlay1` do to `xmm0` and `xmm1` (or `xmm2`), with lane `l` of
  the two loads of 32 bytes holding the coefficients at `16l` and
  `32 + 16l`, and the zetas of the blocks there in lane `l` of `ymm13`
  (`yzetaS`, or `vpermq` of eight zetas).

`NTT⁻¹` then scales every coefficient (`yscale`). The multiplications run
inside `withMxcsr` as in the SSE2 code: for `vg_mldsa_multiply*_ntt_avx2`,
through the last 8 bytes of `h`, whose last eight coefficients are loaded
to `ymm6` first; the loop stores the first 248, and the last eight are
stored after MXCSR is loaded back. Every function clears the upper halves of
the vector registers before returning (`vzeroupper`). Every address and
branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov withMxcsr rcxLoop toY yconst)

/-- `q` in the doublewords of `ymm15` and `-q⁻¹ mod 2³²` in those of `ymm14`. -/
def yconsts : List Instr := yconst .xmm15 8380417 ++ yconst .xmm14 4236238847

/-- `vzeroupper`. -/
def yepi : List Instr := [.vop .vzeroupper]

/-! ## The NTT and its inverse -/

/-- The zeta at `[r8]` in every doubleword of both lanes of `ymm13`, and in
those of `ymm12`: `vzeta 0` in each lane. -/
def yzeta1 : List Instr :=
  .vbroadcasti128 .xmm13 (at_ .r8 0) :: toY [.xop (.pshufd .xmm13 .xmm13 0), .xop (.pshufd .xmm12 .xmm13 0xF5)]

/-- The four zetas at `[r8]` in both lanes, arranged by `vpshufd` with `o₀`
into lane 0 of `ymm13` and with `o₁` into lane 1 (through `ymm2`), and its
odd doublewords in the even ones of `ymm12`. -/
def yzetaS (o₀ o₁ : BitVec 8) : List Instr :=
  .vbroadcasti128 .xmm13 (at_ .r8 0) ::
    toY [.xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)] ++
    [.vop (.vpblendd .l256 .xmm13 .xmm13 .xmm2 0xF0)] ++ toY [.xop (.pshufd .xmm12 .xmm13 0xF5)]

/-- A layer with `len ≥ 8` and butterflies `bf`: its `128 / len` blocks, the
first with the zeta `k`, the zeta pointer moving by `dz` bytes. -/
def ylay (bf : List Instr) (len k : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ leaR .r8 .rsi (4 * k) ++
    [.mov32 .rax (.imm (BitVec.ofNat 32 (128 / len)))])) <|
  .loop (.seq (.block (yzeta1 ++ [.alu .add .r8 (.imm dz)]))
    (.seq (rcxLoop (len / 8) ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0),
        .vmovdquLoad .l256 .xmm1 (at_ .rdx (4 * len))] ++ toY bf ++
        [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (4 * len)) .xmm3,
          .alu .add .rdx (.imm 32)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rax (.imm 1)]))) .ne

/-- The layer with `len = 4`, two blocks at a time: the first with the zeta
`k`, the zetas of a pair at `[r8]` arranged by `yzetaS o₀ o₁`, the zeta
pointer moving by `dz` bytes. -/
def ylay4 (bf : List Instr) (k : Nat) (o₀ o₁ : BitVec 8) (dz : BitVec 32) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ leaR .r8 .rsi (4 * k))) <|
  rcxLoop 16 ([.vmovdquLoad .l256 .xmm4 (at_ .rdx 0), .vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++
    yzetaS o₀ o₁ ++
    [.alu .add .r8 (.imm dz), .vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20),
      .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++ toY bf ++
    [.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20), .vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31),
      .vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5,
      .alu .add .rdx (.imm 64)])

/-- `vlay2`'s gathering of the halves of two blocks (`Ntt.lean`). -/
def gath2 : List Instr := [xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1, xmov .xmm1 .xmm2]

/-- `vlay2`'s interleaving back. -/
def scat2 : List Instr := [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3]

/-- The layer with `len = 2`, four blocks at a time: in each lane, `vlay2`'s
two (`gath2`, `bf`, `scat2`), with their zetas from `[r8]` arranged by
`yzetaS o₀ o₁`, the zeta pointer moving by `dz` bytes. -/
def ylay2 (bf : List Instr) (k : Nat) (o₀ o₁ : BitVec 8) (dz : BitVec 32) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ leaR .r8 .rsi (4 * k))) <|
  rcxLoop 16 ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx 32)] ++
    yzetaS o₀ o₁ ++ [.alu .add .r8 (.imm dz)] ++ toY (gath2 ++ bf ++ scat2) ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64)])

/-- `vlay1`'s gathering of the pairs of four blocks (`Ntt.lean`). -/
def gath1 : List Instr :=
  [.xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8), xmov .xmm1 .xmm0,
    xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2]

/-- `vlay1`'s interleaving back. -/
def scat1 : List Instr := [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3]

/-- The eight zetas at `[r8]` in the order the lanes of `ylay1` take them
for `NTT`: the first two and the fifth and sixth in lane 0, the others in
lane 1 (`vpermq`). -/
def yzeta8 : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (at_ .r8 0), .vop (.vpermq .xmm13 .xmm13 0xD8)] ++
    toY [.xop (.pshufd .xmm12 .xmm13 0xF5)]

/-- The same for `NTT⁻¹`, whose blocks take the zetas in decreasing order:
the eighth, seventh, fourth and third in lane 0, the others in lane 1. -/
def yzeta8R : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (at_ .r8 0), .vop (.vpermq .xmm13 .xmm13 0x27)] ++
    toY [.xop (.pshufd .xmm13 .xmm13 0xB1), .xop (.pshufd .xmm12 .xmm13 0xF5)]

/-- The layer with `len = 1`, eight blocks at a time: in each lane,
`vlay1`'s four, with their zetas from `[r8]` (`zl`), the zeta pointer moving
by `dz` bytes. -/
def ylay1 (bf : List Instr) (k : Nat) (zl : List Instr) (dz : BitVec 32) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ leaR .r8 .rsi (4 * k))) <|
  rcxLoop 16 ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm2 (at_ .rdx 32)] ++ zl ++
    [.alu .add .r8 (.imm dz)] ++ toY (gath1 ++ bf ++ scat1) ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64)])

/-- Every coefficient times `256⁻¹ mod q`: `vscale` in each lane. -/
def yscale : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ yconst .xmm13 16382 ++ [.vop (.vmovdqa .l256 .xmm12 .xmm13)]))
    (rcxLoop 32 ([.vmovdquLoad .l256 .xmm3 (at_ .rdx 0)] ++ toY (vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++
      vcsub .xmm3 .xmm2) ++ [.vmovdquStore .l256 (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 32)]))

/-- The table and the constants. -/
def ypro : List Instr := dwordTab zmTab 256 .rsi ++ yconsts

def nttAvx2 : Prog isa := withMxcsr .rsi 768 <|
  .seq (.block ypro) (.seq (ylay vbfly 128 1 4) (.seq (ylay vbfly 64 2 4) (.seq (ylay vbfly 32 4 4)
    (.seq (ylay vbfly 16 8 4) (.seq (ylay vbfly 8 16 4) (.seq (ylay4 vbfly 32 0x00 0x55 8)
      (.seq (ylay2 vbfly 64 0xA0 0xF5 16) (.seq (ylay1 vbfly 128 yzeta8 32) (.block yepi)))))))))

def nttInvAvx2 : Prog isa := withMxcsr .rsi 768 <|
  .seq (.block ypro) (.seq (ylay1 vibfly 248 yzeta8R (-32)) (.seq (ylay2 vibfly 124 0x5F 0x0A (-16))
    (.seq (ylay4 vibfly 62 0x55 0x00 (-8)) (.seq (ylay vibfly 8 31 (-4)) (.seq (ylay vibfly 16 15 (-4))
      (.seq (ylay vibfly 32 7 (-4)) (.seq (ylay vibfly 64 3 (-4)) (.seq (ylay vibfly 128 1 (-4))
        (.seq yscale (.block yepi))))))))))

/-! ## Products -/

/-- The constants and `2⁶⁴ mod q` in the doublewords of `ymm11`. -/
def ymulPro : List Instr := yconsts ++ yconst .xmm11 2365951

/-- The coefficients of `f`, `g` and `h` to `ymm3`, `ymm13` and `ymm5`. -/
def ymulLoads : List Instr :=
  [.vmovdquLoad .l256 .xmm3 (at_ .rsi 0), .vmovdquLoad .l256 .xmm13 (at_ .rdx 0),
    .vmovdquLoad .l256 .xmm5 (at_ .rdi 0)]

/-- Store `ymm3` to `h` and advance the three pointers. -/
def ymulTail : List Instr :=
  [.vmovdquStore .l256 (at_ .rdi 0) .xmm3, .alu .add .rdi (.imm 32), .alu .add .rsi (.imm 32),
    .alu .add .rdx (.imm 32)]

/-- The last eight coefficients, with those of `h` in `ymm6`, to `ymm3`. -/
def ymulLast (core : List Instr) : List Instr :=
  [.vmovdquLoad .l256 .xmm3 (at_ .rsi 0), .vmovdquLoad .l256 .xmm13 (at_ .rdx 0),
    .vop (.vmovdqa .l256 .xmm5 .xmm6)] ++ toY core

/-- `mulFn` on eight coefficients at a time. -/
def ymulFn (core : List Instr) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rdi), .vmovdquLoad .l256 .xmm6 (at_ .rdi 992)])
    (.seq (withMxcsr .r8 1016
        (.seq (.block ymulPro) (.seq (rcxLoop 31 (ymulLoads ++ toY core ++ ymulTail)) (.block (ymulLast core)))))
      (.block ([.vmovdquStore .l256 (at_ .rdi 0) .xmm3] ++ yepi)))

def mulAvx2 : Prog isa := ymulFn mulCore

def mulAddAvx2 : Prog isa := ymulFn mulAddCore

/-! ## Sums and differences -/

/-- The body of `add` and `sub` on eight coefficients at a time. -/
def yaccBody (op : XBinOp) (fix : List Instr) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi 0), .vmovdquLoad .l256 .xmm1 (at_ .rsi 0)] ++ toY (xb op .xmm0 .xmm1 :: fix) ++
    [.vmovdquStore .l256 (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 32), .alu .add .rsi (.imm 32)]

def addAvx2 : Prog isa :=
  .seq (.block (yconst .xmm15 8380417)) (.seq (rcxLoop 32 (yaccBody .paddd (vcsub .xmm0 .xmm2))) (.block yepi))

def subAvx2 : Prog isa :=
  .seq (.block (yconst .xmm15 8380417)) (.seq (rcxLoop 32 (yaccBody .psubd (vcadd .xmm0 .xmm2))) (.block yepi))

/-- The AVX2 code. -/
def Backend.avx2 : Backend :=
  ⟨nttAvx2, nttInvAvx2, mulAvx2, mulAddAvx2, addAvx2, subAvx2, Round.highBitsAvx2,
    Round.lowBitsAvx2, Round.normLtAvx2, Round.makeHintAvx2, Round.useHintAvx2, Sample.Rej4.rejNTT4Avx2,
    Sample.Mask4.expandMask4Avx2, "_avx2"⟩

end VG.Impl.MlDsa.X86_64.Arith

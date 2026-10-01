import VerifiedGarbage.Impl.MlKem.X86_64.Mul
import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-KEM on x86-64: `vg_mlkem_multiply_ntts_avx2`

`multiplyNTTsAvx2(h = rdi, f = rsi, g = rdx, scratch = rcx)` is
`vg_mlkem_multiply_ntts` (`Mul.lean`) on sixteen pairs of coefficients at a
time, eight in each 128-bit lane of AVX2 registers (`Avx.lean`): 8 times,
with `rsi`, `rdx` and `rdi` at 32 coefficients of `f`, `g` and `h`, `r8` at
their sixteen `γ`s and `rcx` counting down, it loads 128 bytes of `f` and
of `g` into four registers each (lane `l` of register `t` holding
coefficients `8t + 4l` to `8t + 4l + 3` of the 32), and runs the SSE2
code's `deint`, `vbase` and `vinter` on each lane, so that lane `l` holds
the pairs of coefficients `8t + 4l` to `8t + 4l + 3`, `t < 4`. The table
holds the `γ`s in that order (`gTabY`): word `e` of lane `l` of the sixteen
of iteration `i` is `γ` of pair `16i + 4⌊e/2⌋ + (e mod 2) + 2l`. The
stores of the products then put each coefficient back in its place.

It runs with MXCSR `0x1FBF` (`withMxcsr`), like `vg_mlkem_multiply_ntts`,
and clears the upper halves of the vector registers (`vzeroupper`) before
returning, for the SSE code its callers run next. Every address and branch
depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The `γ` of word `p` of the table (see above). -/
def gIdxY (p : Nat) : Nat := 16 * (p / 16) + 4 * (p % 8 / 2) + p % 2 + 2 * (p % 16 / 8)

/-- The table of `vg_mlkem_multiply_ntts_avx2`. -/
def gTabY (p : Nat) : Nat := gTab (gIdxY p)

/-- `deint` (`Mul.lean`) on registers loaded already: the even doublewords
of `a, b, c, d` as the words of `a`, and the odd ones as those of `x`, with
the temporary `y`. -/
def deintS (a b c d x y : XReg) : List Instr :=
  [.xop (.pshufd a a 0xD8), .xop (.pshufd b b 0xD8), .xop (.pshufd c c 0xD8), .xop (.pshufd d d 0xD8),
    xmov x a, xb .punpckhqdq x b, xb .punpcklqdq a b, xmov y c, xb .punpckhqdq y d, xb .punpcklqdq c d,
    xb .packssdw a c, xb .packssdw x y]

/-- `vinter` (`Mul.lean`) but for its stores: `h₀` and `h₁` interleaved as
doublewords in `xmm1`, `xmm5`, `xmm3` and `xmm6`. -/
def vinterS : List Instr :=
  [xmov .xmm3 .xmm1, xb .punpckhwd .xmm3 .xmm2, xb .punpcklwd .xmm1 .xmm2, xb .pxor .xmm4 .xmm4,
    xmov .xmm5 .xmm1, xb .punpckhwd .xmm5 .xmm4, xb .punpcklwd .xmm1 .xmm4, xmov .xmm6 .xmm3,
    xb .punpckhwd .xmm6 .xmm4, xb .punpcklwd .xmm3 .xmm4]

/-- 128 bytes at `[p]` into `ymm a, b, c, d`. -/
def yload4 (p : Reg) (a b c d : XReg) : List Instr :=
  [.vmovdquLoad .l256 a (at_ p 0), .vmovdquLoad .l256 b (at_ p 32), .vmovdquLoad .l256 c (at_ p 64),
    .vmovdquLoad .l256 d (at_ p 96)]

def mulBodyY : List Instr :=
  yload4 .rsi .xmm0 .xmm1 .xmm2 .xmm3 ++ toY (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5) ++
    yload4 .rdx .xmm6 .xmm7 .xmm8 .xmm9 ++ toY (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11) ++
    [.vmovdquLoad .l256 .xmm13 (at_ .r8 0)] ++ toY vbase ++ toY vinterS ++
    [.vmovdquStore .l256 (at_ .rdi 0) .xmm1, .vmovdquStore .l256 (at_ .rdi 32) .xmm5,
      .vmovdquStore .l256 (at_ .rdi 64) .xmm3, .vmovdquStore .l256 (at_ .rdi 96) .xmm6,
      .alu .add .rsi (.imm 128), .alu .add .rdx (.imm 128), .alu .add .rdi (.imm 128), .alu .add .r8 (.imm 32)]

/-- The table, the constants, and `r8` at the table. -/
def mulProY : List Instr :=
  wordTab gTabY 128 .r10 0 ++ yconsts ++ yconst .xmm12 0x05490549 ++ [.mov .r8 (.reg .r10)]

def multiplyNTTsAvx2 : Prog isa :=
  .seq (.block [.mov .r10 (.reg .rcx)])
    (withMxcsr .r10 768 (.seq (.block mulProY) (.seq (rcxLoop 8 mulBodyY) (.block [.vop .vzeroupper]))))

end VG.Impl.MlKem.X86_64

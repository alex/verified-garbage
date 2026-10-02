import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec
import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-DSA on x86-64: rounding with AVX2

`vg_mldsa_high_bits_avx2`, `vg_mldsa_low_bits_avx2`,
`vg_mldsa_norm_lt_avx2` and `vg_mldsa_make_hint_avx2` are
`vg_mldsa_high_bits`, `vg_mldsa_low_bits`, `vg_mldsa_norm_lt` and
`vg_mldsa_make_hint` (`Round.lean`) on eight
coefficients at a time, in the doublewords of `ymm` registers: in each
128-bit lane, the VEX.256 form (`toY`) of SSE2 code on the four doublewords
of an `xmm` register (`hbX`, `lbX`, `nlX`, `mhX`), with `rdi` and `r10` at the eight
coefficients of `r` and `out` and `rcx` counting down the 32 vectors.

`Decompose` is the reference implementation's, as in `Round.lean`:
`f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` and `r₁ = f mod m`, but in 32
bits, which hold every intermediate value, with the multiplication by `M` a
sum of shifts (`mulX`: `1025 = 2¹⁰ + 1` and `11275 = 2¹³ + 2¹¹ + 2¹⁰ + 2³ +
2 + 1`), and, as `f ≤ m`, `r₁` is `f` ANDed with the sign of `f - m`
(`psrad` by 31). `r₀ = a - r₁ · 2γ₂` likewise multiplies by shifts
(`2γ₂ = 2¹⁹ - 2⁹` or `2¹⁷ + 2¹⁵ + 2¹⁴ + 2¹³ + 2¹¹`), plus `q` if negative
(`vcadd`). There are no multiplication instructions, and no branch on data:
the functions branch once on the public `γ₂`, and every address depends
only on the pointers. Each clears the upper halves of the vector registers
before returning (`vzeroupper`).
-/

namespace VG.Impl.MlDsa.X86_64.Round

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov rcxLoop toY yconst at_)
open VG.Impl.MlDsa.X86_64.Arith (vcadd vcsub)

/-- The shifts whose sum, with 1, is `M`. -/
def dSh (g : Nat) : List Nat := if g = 261888 then [10] else [1, 3, 10, 11, 13]

/-- `xmm0 ← xmm0 · (1 + Σ 2^k)`, through `xmm1` and `xmm2`. -/
def mulX (sh : List Nat) : List Instr :=
  xmov .xmm1 .xmm0 :: sh.flatMap fun k =>
    [xmov .xmm2 .xmm1, .xop (.shift .pslld .xmm2 (BitVec.ofNat 8 k)), xb .paddd .xmm0 .xmm2]

/-- `xmm0 ← r₁` of `xmm0`, with `127`, `2^(S-1)` and `m` in `xmm8`, `xmm9` and `xmm10`. -/
def hbX (g : Nat) : List Instr :=
  [xb .paddd .xmm0 .xmm8, .xop (.shift .psrld .xmm0 7)] ++ mulX (dSh g) ++
    [xb .paddd .xmm0 .xmm9, .xop (.shift .psrld .xmm0 (BitVec.ofNat 8 (dShift g))), xmov .xmm1 .xmm0,
      xb .psubd .xmm1 .xmm10, .xop (.shift .psrad .xmm1 31), xb .pand .xmm0 .xmm1]

/-- `xmm1 ← xmm0 · 2γ₂`, through `xmm2`. -/
def mul2X (g : Nat) : List Instr :=
  if g = 261888 then
    [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 19), xmov .xmm2 .xmm0, .xop (.shift .pslld .xmm2 9),
      xb .psubd .xmm1 .xmm2]
  else
    [xmov .xmm1 .xmm0, .xop (.shift .pslld .xmm1 11)] ++ [13, 14, 15, 17].flatMap fun k =>
      [xmov .xmm2 .xmm0, .xop (.shift .pslld .xmm2 (BitVec.ofNat 8 k)), xb .paddd .xmm1 .xmm2]

/-- `xmm3 ← r₀` of `xmm0`, with `q` also in `xmm15`. -/
def lbX (g : Nat) : List Instr :=
  xmov .xmm3 .xmm0 :: hbX g ++ mul2X g ++ xb .psubd .xmm3 .xmm1 :: vcadd .xmm3 .xmm1

/-- The constants of `hbX` and `lbX`. -/
def yC (g : Nat) : List Instr :=
  yconst .xmm8 127 ++ yconst .xmm9 (BitVec.ofNat 32 (dAdd g)) ++ yconst .xmm10 (BitVec.ofNat 32 (dMod g)) ++
    yconst .xmm15 8380417

/-- Eight coefficients of `r` (at `rdi`) to `out` (at `r10`), through `x`, the result left in `ymm d`. -/
def bitsBodyY (x : List Instr) (d : XReg) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdi 0)] ++ toY x ++
    [.vmovdquStore .l256 (at_ .r10 0) d, .alu .add .rdi (.imm 32), .alu .add .r10 (.imm 32)]

/-- `γ₂` compared, the output pointer to `r10`, and the loop of `γ₂`, `x g` leaving its result in `ymm d`. -/
def bitsY (x : Nat → List Instr) (d : XReg) : Prog isa :=
  .seq (.block (gammaCmp .rsi ++ [.mov .r10 (.reg .rdx)]))
    (.seq (.ite .e (.seq (.block (yC g32)) (rcxLoop 32 (bitsBodyY (x g32) d)))
      (.seq (.block (yC g88)) (rcxLoop 32 (bitsBodyY (x g88) d)))) (.block [.vop .vzeroupper]))

def highBitsAvx2 : Prog isa := bitsY hbX .xmm0

def lowBitsAvx2 : Prog isa := bitsY lbX .xmm3

/-! ## `vg_mldsa_norm_lt_avx2`

The bound is first clamped to `q` (a branch on the public bound), which
changes no result, as every reduced coefficient is less than `q`; then the
differences `a - b` and `(q - b) - a` fit in 32 bits, and one of them is
negative exactly when `a < b` or `q - a < b`. Each doubleword of `ymm10`
ANDs the ORs of the differences of its coefficients; its top bit stays set
while all of them are good. At the end the top bits are spread over their
doublewords (`vpsrad` by 31), and `vpmovmskb` gathers the top bits of the
32 bytes: the result is `(mask + 1) >> 32`, 1 exactly when every bit is set. -/

/-- `ymm10 ← ymm10 & ((a - b) | ((q - b) - a))` for `a` in `xmm0`, `b` in `xmm8`, `q - b` in `xmm9`. -/
def nlX : List Instr :=
  [xmov .xmm1 .xmm0, xb .psubd .xmm1 .xmm8, xmov .xmm2 .xmm9, xb .psubd .xmm2 .xmm0, xb .por .xmm1 .xmm2,
    xb .pand .xmm10 .xmm1]

def nlBodyY : List Instr := [.vmovdquLoad .l256 .xmm0 (at_ .rdi 0)] ++ toY nlX ++ [.alu .add .rdi (.imm 32)]

/-- The low doubleword of `rax` in each doubleword of `ymm r`. -/
def ybcast (r : XReg) : List Instr := [.vop (.vmovq r .rax), .vop (.vpbroadcastd .l256 r r)]

/-- `b` in `ymm8`, `q - b` in `ymm9` and all ones in `ymm10`. -/
def nlConsts : List Instr :=
  [.mov32 .rax (.reg .rsi)] ++ ybcast .xmm8 ++ [.mov32 .rax (.imm qImm), .alu32 .sub .rax (.reg .rsi)] ++
    ybcast .xmm9 ++ yconst .xmm10 0xFFFFFFFF

def nlEnd : List Instr :=
  toY [.xop (.shift .psrad .xmm10 31)] ++ [.vpmovmskb .l256 .rax .xmm10, .vop .vzeroupper] ++
    [.alu .add .rax (.imm 1), .shift .shr .rax 32]

/-- The bound, clamped to `q`. -/
def nlPro : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .alu32 .cmp .rsi (.imm qImm)]) (.ite .b (.block []) (.block [.mov32 .rsi (.imm qImm)]))

def normLtAvx2 : Prog isa := .seq nlPro (.seq (.block nlConsts) (.seq (rcxLoop 32 nlBodyY) (.block nlEnd)))

/-! ## `vg_mldsa_make_hint_avx2`

In each lane, `r₁` of `r` and of `(r + z) mod q` (`hbX` twice, with `vcsub`
between), XORed, is nonzero (`(x + 63) >> 6`, as `x < 64`) exactly when the
hint is 1 (`mhX`); the eight hints are stored. Their count is the sum of the
nibbles of the byte mask of the hints shifted to the top bit of their low
bytes (`vpmovmskb`, which has hint `i` at bit `4i`): three shifts and
additions put it in the low nibble (`cntH`), which is added to `r9`. -/

/-- `r₁` of `r` to `xmm3`, and `(r + z) mod q` to `xmm0`, with `r` in `xmm4` and `z` in `xmm5`. -/
def mhMid : List Instr := [xmov .xmm3 .xmm0, xmov .xmm0 .xmm4, xb .paddd .xmm0 .xmm5] ++ vcsub .xmm0 .xmm1

/-- The hint from the two `r₁`, to `xmm0`, and shifted to bit 7, to `xmm1`. -/
def mhTail : List Instr :=
  [xb .pxor .xmm0 .xmm3, xb .paddd .xmm0 .xmm11, .xop (.shift .psrld .xmm0 6), xmov .xmm1 .xmm0,
    .xop (.shift .pslld .xmm1 7)]

/-- `xmm0 ← the hints` of `r` in `xmm0` and `z` in `xmm5`, and `xmm1 ← xmm0 << 7`, with `63` in `xmm11`. -/
def mhX (g : Nat) : List Instr := [xmov .xmm4 .xmm0] ++ hbX g ++ mhMid ++ hbX g ++ mhTail

/-- `r9 ← r9 +` the sum of the nibbles of `eax`, through `rdx`. -/
def cntH : List Instr :=
  [.mov32 .rdx (.reg .rax), .shift32 .shr .rdx 4, .alu32 .add .rax (.reg .rdx),
    .mov32 .rdx (.reg .rax), .shift32 .shr .rdx 8, .alu32 .add .rax (.reg .rdx),
    .mov32 .rdx (.reg .rax), .shift32 .shr .rdx 16, .alu32 .add .rax (.reg .rdx),
    .alu32 .and .rax (.imm 15), .alu .add .r9 (.reg .rax)]

/-- Eight coefficients of `r` (at `rsi`) and `z` (at `rdi`) to the hints at `r10`, and their count added to `r9`. -/
def mhBodyY (g : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rsi 0), .vmovdquLoad .l256 .xmm5 (at_ .rdi 0)] ++ toY (mhX g) ++
    [.vmovdquStore .l256 (at_ .r10 0) .xmm0, .vpmovmskb .l256 .rax .xmm1] ++ cntH ++
    [.alu .add .rdi (.imm 32), .alu .add .rsi (.imm 32), .alu .add .r10 (.imm 32)]

def mhY (g : Nat) : Prog isa := .seq (.block (yC g ++ yconst .xmm11 63)) (rcxLoop 32 (mhBodyY g))

def makeHintAvx2 : Prog isa :=
  .seq (.block (gammaCmp .rdx ++ [.mov .r10 (.reg .rcx), .mov32 .r9 (.imm 0)]))
    (.seq (.ite .e (mhY g32) (mhY g88)) (.block [.mov .rax (.reg .r9), .vop .vzeroupper]))

end VG.Impl.MlDsa.X86_64.Round

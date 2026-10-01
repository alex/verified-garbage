import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec
import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-DSA on x86-64: rounding with AVX2

`vg_mldsa_high_bits_avx2` and `vg_mldsa_low_bits_avx2` are
`vg_mldsa_high_bits` and `vg_mldsa_low_bits` (`Round.lean`) on eight
coefficients at a time, in the doublewords of `ymm` registers: in each
128-bit lane, the VEX.256 form (`toY`) of SSE2 code on the four doublewords
of an `xmm` register (`hbX`, `lbX`), with `rdi` and `r10` at the eight
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
open VG.Impl.MlDsa.X86_64.Arith (vcadd)

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

end VG.Impl.MlDsa.X86_64.Round

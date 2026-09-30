import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Common

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_sample_in_ball`

`sampleInBall(ctilde = r0, len = r1, tau = r2, c = r3, scratch = [sp]) ->
r0` (see `Common.lean` for the layout; `scratch` is loaded from the stack
into `r12` first) squeezes 272 bytes of SHAKE256 of the `len` bytes of `c̃`
(2 blocks; the least bound of FIPS 204 Appendix C is 221 bytes, the
contract's largest 1088), zeroes `c`, and runs `SampleInBall`'s loop over the
264 bytes after the first 8, as on x86-64, with `r0` at the byte, `r2` = `i`
(from `256 - τ`), the sign bits not yet used in `r1` (low word) and `r4`
(high word; the first 8 bytes, as a `u64`, shifted right once per
coefficient set) and `r3` counting down: while `i < 256`, a byte `j ≤ i` (in
`r8`) sets `c[i] ← c[j]` and `c[j] ← ±1` (1, or `q - 1` if the next sign bit
is 1), and increments `i`. It returns `i >> 8`: 1 if `i = 256`, and 0
otherwise.

Its branches and addresses depend on the SHAKE256 output, a function of
`c̃`, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.Arm.Sample

open VG.Arm

/-- The 256 coefficients of `c` zeroed, through `r0` and `r12`, `r3` counting. -/
def bZero : Prog isa :=
  .seq (.block [.mov .r12 (.imm 0), .mov .r0 (.reg .r5), .mov .r3 (.imm 256)])
    (.loop (.block [.str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]) .ne)

/-- The sign bits in `r1` and `r4`, `i = 256 - τ` in `r2`, and `r0` at the
byte after them. -/
def bSetup : List Instr :=
  [.ldr .r1 .r6 840, .ldr .r4 .r6 844, .mov .r2 (.imm 256), .dp .sub .r2 .r2 (.reg .r7),
    .dp .add .r0 .r6 (.imm 848)]

/-- `c[i] ← c[j]`, `c[j] ← ±1`, the sign bits shifted, `i` incremented. -/
def bSet : Prog isa :=
  .seq (.block [.dp .add .r10 .r5 (.shifted .r8 .lsl 2), .ldr .r11 .r10 0, .dp .add .r12 .r5 (.shifted .r2 .lsl 2),
      .str .r11 .r12 0, .dp .and .r11 .r1 (.imm 1), .cmp .r11 (.imm 0)])
    (.seq (.ite .eq (.block [.mov .r11 (.imm 1)]) (.block [.movw .r11 0xE000, .movt .r11 0x7F]))
      (.block [.str .r11 .r10 0, .mov .r1 (.shifted .r1 .lsr 1), .dp .orr .r1 .r1 (.shifted .r4 .lsl 31),
        .mov .r4 (.shifted .r4 .lsr 1), .dp .add .r2 .r2 (.imm 1)]))

/-- The byte `j` at `r0`, into `r8`, rejected if `i < j`. -/
def bTry : Prog isa :=
  .seq (.block [.ldrb .r8 .r0 0, .dp .sub .r11 .r2 (.reg .r8), .mov .r11 (.shifted .r11 .lsr 31),
      .cmp .r11 (.imm 0)])
    (.ite .eq bSet (.block []))

def bBody : Prog isa := .seq (.block jFull) (.seq (.ite .eq (.block []) bTry) (.block (step 1)))

def bLoop : Prog isa := .seq (.block (bSetup ++ [.mov .r3 (.imm 264)])) (.loop bBody .ne)

def sampleInBall : Prog isa :=
  .seq (.block (.ldrSp .r12 0 :: pro .r12 .r3 (.reg .r2) (.reg .r1) .r0))
    (.seq (sponge 136 272) (.seq bZero (.seq bLoop (.block (retJ ++ epi)))))

end VG.Impl.MlDsa.Arm.Sample

import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_sample_in_ball`

`sampleInBall(ctilde = x0, len = x1, tau = w2, c = x3, scratch = x4) -> w0`
(see `Common.lean` for the layout) squeezes 272 bytes of SHAKE256 of the
`len` bytes of `c̃` (2 blocks; the least bound of FIPS 204 Appendix C is 221
bytes, the contract's largest 1088), zeroes `c`, and runs `SampleInBall`'s
loop over the 264 bytes after the first 8, with `x2` at the byte, `x10` =
`i` (from `256 - τ`), `x11` = `256 - i`, `x9` the sign bits not yet used
(the first 8 bytes, as a `u64`, shifted right once per coefficient set) and
`x5` counting down: while `i < 256`, a byte `j ≤ i` sets `c[i] ← c[j]` and
`c[j] ← ±1` (1, or `q - 1` if the next sign bit is 1: `1 + (q - 2) · bit`),
and increments `i`. It returns `i >> 8`: 1 if `i = 256`, and 0 otherwise.

Its branches and addresses depend on the SHAKE256 output, a function of
`c̃`, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.AArch64.Sample

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)

/-- `c[i] ← c[j]`, `c[j] ← ±1`, the sign bits shifted, `i` incremented. -/
def bSet : List Instr :=
  [.lsl .x .x8 .x6 2, .add .x .x8 .x26 .x8, .lsl .x .x13 .x10 2, .add .x .x13 .x26 .x13,
    .ldr .w .x14 .x8 0, .str .w .x14 .x13 0, .logic .and .x .x14 .x9 .x15,
    .madd .x .x14 .x14 .x12 .x15, .str .w .x14 .x8 0, .lsr .x .x9 .x9 1, .addImm .x .x10 .x10 1,
    .subImm .x .x11 .x11 1]

/-- The byte `j` at `x2`, rejected if `i < j`. -/
def bTry : Prog isa :=
  .seq (.block [.ldrb .x6 .x2 0, .sub .x .x7 .x10 .x6, .lsr .x .x7 .x7 63])
    (.ite (.nonzero .x .x7) (.block []) (.block bSet))

def bBody : Prog isa :=
  .seq (.ite (.zero .x .x11) (.block []) bTry) (.block [.addImm .x .x2 .x2 1, .subImm .x .x5 .x5 1])

/-- The loop's registers: the sign bits, `i = 256 - τ`, and `x2` at the byte
after them. -/
def bSetup : List Instr :=
  [.ldr .x .x9 .x25 840, .movz .x .x10 256 0, .sub .x .x10 .x10 .x27, mov .x11 .x27,
    .addImm .x .x2 .x25 848, .movz .x .x5 264 0] ++ movQ .x12 ++
    [.subImm .x .x12 .x12 2, .movz .x .x15 1 0]

def bLoop : Prog isa := .seq (.block bSetup) (.loop bBody (.nonzero .x .x5))

def sampleInBall : Prog isa :=
  .seq (.block (pro .x4 .x3 (.addImm .w .x27 .x2 0) (mov .x4 .x1)))
    (.seq (sponge 136 272) (.seq zeroPoly (.seq bLoop (.block (.lsr .x .x0 .x10 8 :: epi)))))

end VG.Impl.MlDsa.AArch64.Sample

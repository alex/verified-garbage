import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_ntt_poly`

`rejNTT(seed = x0, a = x1, scratch = x2) -> w0` (see `Common.lean` for the
layout) squeezes 1008 bytes of SHAKE128 of the 34 bytes of the seed (6
blocks; the least bound of FIPS 204 Appendix C is 894 bytes, the contract's
largest 1344), zeroes `a`, and runs the 336 iterations of `RejNTTPoly`'s
loop on 3 bytes each, with `x2` at the 3 bytes of the iteration, `x3` at
coefficient `j` of `a`, `x4` = `256 - j` and `x5` counting down: while
`j < 256`, the value of the 3 bytes (`b₀ + 2⁸ b₁ + 2¹⁶ (b₂ mod 2⁷)`, in
`x11`) is stored as coefficient `j`, and `j` is incremented if it is less
than `q`, without a branch (as `vg_mlkem_sample_ntt` does), so that a
rejected value is overwritten by the next. It returns 1 if `j = 256`, and 0
otherwise.

The loop's branches and addresses depend on the XOF output, a function of
the seed, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.AArch64.Sample

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)

/-- The value of the 3 bytes at `x2` in `x11`. -/
def rnChunk : List Instr :=
  [.ldrb .x6 .x2 0, .ldrb .x7 .x2 1, .ldrb .x8 .x2 2, .addImm .x .x2 .x2 3, .subImm .x .x5 .x5 1,
    .logic .and .x .x8 .x8 .x10, .lsl .x .x8 .x8 16, .lsl .x .x7 .x7 8, .add .x .x11 .x6 .x7,
    .add .x .x11 .x11 .x8]

/-- Store `x11` as coefficient `j`, and count it if it is less than `q`
(`x9`). -/
def rnAccept : List Instr :=
  [.sub .x .x13 .x11 .x9, .lsr .x .x14 .x13 63, .str .w .x11 .x3 0, .lsl .x .x15 .x14 2,
    .add .x .x3 .x3 .x15, .sub .x .x4 .x4 .x14]

def rnBody : Prog isa := .seq (.block rnChunk) (.ite (.zero .x .x4) (.block []) (.block rnAccept))

/-- The loop's registers. -/
def rnSetup : List Instr :=
  [.addImm .x .x2 .x25 840, mov .x3 .x26, .movz .x .x4 256 0, .movz .x .x5 336 0] ++ movQ .x9 ++
    [.movz .x .x10 127 0]

def rnLoop : Prog isa := .seq (.block rnSetup) (.loop rnBody (.nonzero .x .x5))

def rejNTTWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (pro .x2 .x1 (.movz .x .x27 0 0) (.movz .x .x4 34 0)))
    (.seq (spongeWith c 168 1008) (.seq zeroPoly (.seq rnLoop (.block (retZ ++ epi)))))

def rejNTT := rejNTTWith .scalar

end VG.Impl.MlDsa.AArch64.Sample

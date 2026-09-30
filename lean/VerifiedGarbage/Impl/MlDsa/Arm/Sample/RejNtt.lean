import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Common

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_ntt_poly`

`rejNTT(seed = r0, a = r1, scratch = r2) -> r0` (see `Common.lean` for the
layout) squeezes 1008 bytes of SHAKE128 of the 34 bytes of the seed (6
blocks; the least bound of FIPS 204 Appendix C is 894 bytes, the contract's
largest 1344), which the 336 iterations of `RejNTTPoly`'s loop take 3 bytes
at a time, as on x86-64. The loop runs 336 times, with `r0` at the 3 bytes
of the iteration, `r2` = `j`, the number of coefficients sampled, `r3`
counting down and `r7` = `q`: while `j < 256`, the value of the 3 bytes
(`b₀ + 2⁸ b₁ + 2¹⁶ (b₂ mod 2⁷)`, in `r10`) is stored to `a[j]` and `j`
incremented if it is less than `q` (the sign bit of `r10 - q`). It returns
`j >> 8`: 1 if `j = 256`, and 0 otherwise.

The loop's branches and the addresses of its stores depend on the XOF
output, a function of the seed, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.Arm.Sample

open VG.Arm

/-- The value of the 3 bytes at `r0` in `r10`. -/
def rnLoad : List Instr :=
  [.ldrb .r8 .r0 0, .ldrb .r9 .r0 1, .ldrb .r10 .r0 2, .mov .r10 (.shifted .r10 .lsl 25),
    .dp .add .r10 .r8 (.shifted .r10 .lsr 9), .dp .add .r10 .r10 (.shifted .r9 .lsl 8)]

/-- Store `r10` to `a[j]` if it is less than `q` (in `r7`). -/
def rnTry : Prog isa :=
  .seq (.block [.dp .sub .r11 .r10 (.reg .r7), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)])
    (.ite .eq (.block []) (.block (storeJ .r10)))

def rnBody : Prog isa :=
  .seq (.block (rnLoad ++ jFull)) (.seq (.ite .eq (.block []) rnTry) (.block (step 3)))

/-- The loop, from the XOF output at `scratch + 840`. -/
def rnLoop : Prog isa :=
  .seq (.block [.dp .add .r0 .r6 (.imm 840), .mov .r2 (.imm 0), .mov .r3 (.imm 336), .movw .r7 0xE001,
      .movt .r7 0x7F])
    (.loop rnBody .ne)

def rejNTT : Prog isa :=
  .seq (.block (pro .r2 .r1 (.imm 0) (.imm 34) .r0))
    (.seq (sponge 168 1008) (.seq rnLoop (.block (retJ ++ epi))))

end VG.Impl.MlDsa.Arm.Sample

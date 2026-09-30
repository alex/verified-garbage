import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Common
import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Stream

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_bounded_poly`

`rejBounded(seed = r0, eta = r1, a = r2, scratch = r3) -> r0` (see
`Common.lean` for the layout) squeezes 544 bytes of SHAKE256 of the 66 bytes
of the seed (4 blocks; the least bound of FIPS 204 Appendix C is 481 bytes,
the contract's largest 1088), which the 544 iterations of `RejBoundedPoly`'s
loop take a byte at a time, as on x86-64. The loop (`rbLoop η`, one for each
`η`, chosen by a branch on the public `η`) runs 544 times, with `r0` at the
byte of the iteration, `r2` = `j`, the number of coefficients sampled, and
`r3` counting down: while `j < 256`, each half-byte `b` of the byte (low
first, in `r9`) that `CoeffFromHalfByte` accepts (`b < 15` for `η = 2`,
`b < 9` for `η = 4`: the sign bit of `b - 15` or `b - 9`) gives the
coefficient `η - (b mod 5)` or `η - b`, stored modulo `q` to `a[j]` (and `j`
incremented; the high half-byte only if `j < 256` still). It returns
`j >> 8`: 1 if `j = 256`, and 0 otherwise.

The coefficient is computed without a branch or a table (`rbVal`): `b mod 5`
by subtracting 10 and then 5, each added back if the result is negative
(from its sign bit), and `q` added to `η - (b mod 5)` if it is negative. So
the loop's branches and the addresses of its stores depend only on which
half-bytes are accepted (and `j`, which counts them), which the contract
lets it leak, not on the coefficients.
-/

namespace VG.Impl.MlDsa.Arm.Sample

open VG.Arm
open VG.Impl.MlDsa.Arm.Pack (addQNeg)

/-- `r9 ← r9 - s` if `s ≤ r9` (`r9 < 2³¹`), with `r11` as the sign bit, for
`s` 10 or 5. -/
def csub (s : Nat) : List Instr :=
  [.dp .sub .r9 .r9 (.imm (BitVec.ofNat 32 s)), .mov .r11 (.shifted .r9 .lsr 31)] ++
    (if s = 10 then [.dp .add .r9 .r9 (.shifted .r11 .lsl 3), .dp .add .r9 .r9 (.shifted .r11 .lsl 1)]
      else [.dp .add .r9 .r9 (.shifted .r11 .lsl 2), .dp .add .r9 .r9 (.reg .r11)])

/-- The coefficient of an accepted half-byte `r9`, modulo `q`, in `r10`:
`η - (b mod 5)` for `η = 2`, `η - b` for `η = 4`. -/
def rbVal : Nat → List Instr
  | 2 => csub 10 ++ csub 5 ++ [.mov .r10 (.imm 2), .dp .sub .r10 .r10 (.reg .r9)] ++ addQNeg .r10 .r11
  | _ => [.mov .r10 (.imm 4), .dp .sub .r10 .r10 (.reg .r9)] ++ addQNeg .r10 .r11

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → Nat
  | 2 => 15
  | _ => 9

/-- Store the coefficient of the half-byte `r9` to `a[j]` if it is accepted. -/
def rbTry (η : Nat) : Prog isa :=
  .seq (.block [.dp .sub .r11 .r9 (.imm (BitVec.ofNat 32 (rbBound η))), .mov .r11 (.shifted .r11 .lsr 31),
      .cmp .r11 (.imm 0)])
    (.ite .eq (.block []) (.block (rbVal η ++ storeJ .r10)))

/-- The byte at `r0` in `r8`, its low half-byte in `r9`, and `Z` set iff `j ≥ 256`. -/
def rbLoad : List Instr :=
  [.ldrb .r8 .r0 0, .mov .r9 (.shifted .r8 .lsl 28), .mov .r9 (.shifted .r9 .lsr 28)] ++ jFull

/-- The high half-byte in `r9`, and `Z` set iff `j ≥ 256`. -/
def rbHi : List Instr := .mov .r9 (.shifted .r8 .lsr 4) :: jFull

def rbBody (η : Nat) : Prog isa :=
  .seq (.block rbLoad)
    (.seq (.ite .eq (.block []) (.seq (rbTry η) (.seq (.block rbHi) (.ite .eq (.block []) (rbTry η)))))
      (.block (step 1)))

/-- The loop, from the XOF output at `scratch + 840`. -/
def rbLoop (η : Nat) : Prog isa :=
  .seq (.block [.dp .add .r0 .r6 (.imm 840), .mov .r2 (.imm 0), .mov .r3 (.imm 544)]) (.loop (rbBody η) .ne)

def rejBounded : Prog isa :=
  .seq (.block (pro .r3 .r2 (.reg .r1) (.imm 66) .r0))
    (.seq (sponge 136 544)
      (.seq (.seq (.block [.cmp .r7 (.imm 2)]) (.ite .eq (rbLoop 2) (rbLoop 4)))
        (.block (retJ ++ epi))))

end VG.Impl.MlDsa.Arm.Sample

import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_bounded_poly`

`rejBounded(seed = x0, eta = w1, a = x2, scratch = x3) -> w0` (see
`Common.lean` for the layout) squeezes 544 bytes of SHAKE256 of the 66 bytes
of the seed (4 blocks; the least bound of FIPS 204 Appendix C is 481 bytes,
the contract's largest 1088), which the 544 iterations of
`RejBoundedPoly`'s loop take a byte at a time. The loop (`rbLoop η`, one for
each `η`, chosen by a branch on the public `η`) runs 544 times, with `x2` at
the byte of the iteration, `x3` at coefficient `j` of `a`, `x4` = `256 - j`
and `x5` counting down: while `j < 256`, each half-byte `b` of the byte (low
first, in `x7`) is tried: the coefficient `η - (b mod 5)` or `η - b` modulo
`q` is stored as coefficient `j`, and `j` is incremented if
`CoeffFromHalfByte` accepts `b` (`b < 15` for `η = 2`, `b < 9` for `η = 4`);
the high half-byte only if `j < 256` still. It returns 1 if `j = 256`, and 0
otherwise.

A try has no branch and no table (`rbTry`): `b mod 5` is computed by
subtracting 10 and then 5, and adding them back where the result is
negative (its sign bit, times the constant, by `madd`), and `q` is added to
`η - (b mod 5)` where that is negative. So the loop's branches and the
addresses of its stores depend only on `j`, which counts the half-bytes
accepted, which the contract lets it leak, not on the coefficients.
-/

namespace VG.Impl.MlDsa.AArch64.Sample

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov csub)

/-- The coefficient of the half-byte `b` (in `x7`) modulo `q`, in `x13`:
`η - (b mod 5)` for `η = 2` (for `b < 15`), `η - b` for `η = 4` (for
`b < 9`), with `η` in `x10`, `q` in `x9`, 10 in `x16` and 5 in `x17`. -/
def rbVal : Nat → List Instr
  | 2 => mov .x13 .x7 :: csub .x13 .x14 .x16 ++ csub .x13 .x14 .x17 ++
      [.sub .x .x13 .x10 .x13, .lsr .x .x14 .x13 63, .madd .x .x13 .x14 .x9 .x13]
  | _ => [.sub .x .x13 .x10 .x7, .lsr .x .x14 .x13 63, .madd .x .x13 .x14 .x9 .x13]

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → Nat
  | 2 => 15
  | _ => 9

/-- Try the half-byte `b` in `x7`: whether it is accepted (less than the
bound in `x15`) in `x12`, its coefficient stored as coefficient `j`, and `j`
incremented if it is accepted. -/
def rbTry (η : Nat) : List Instr :=
  [.sub .x .x8 .x7 .x15, .lsr .x .x12 .x8 63] ++ rbVal η ++
    [.str .w .x13 .x3 0, .lsl .x .x14 .x12 2, .add .x .x3 .x3 .x14, .sub .x .x4 .x4 .x12]

/-- The byte at `x2` in `x6`, its low half-byte in `x7`. -/
def rbLoad : List Instr :=
  [.ldrb .x6 .x2 0, .addImm .x .x2 .x2 1, .subImm .x .x5 .x5 1, .logic .and .x .x7 .x6 .x11]

def rbBody (η : Nat) : Prog isa :=
  .seq (.block rbLoad)
    (.ite (.zero .x .x4) (.block [])
      (.seq (.block (rbTry η ++ [.lsr .x .x7 .x6 4]))
        (.ite (.zero .x .x4) (.block []) (.block (rbTry η)))))

/-- The loop's registers. -/
def rbSetup (η : Nat) : List Instr :=
  [.addImm .x .x2 .x25 840, mov .x3 .x26, .movz .x .x4 256 0, .movz .x .x5 544 0] ++ movQ .x9 ++
    [mov .x10 .x27, .movz .x .x11 15 0, .movz .x .x15 (BitVec.ofNat 16 (rbBound η)) 0,
      .movz .x .x16 10 0, .movz .x .x17 5 0]

def rbLoop (η : Nat) : Prog isa := .seq (.block (rbSetup η)) (.loop (rbBody η) (.nonzero .x .x5))

def rejBoundedWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0)))
    (.seq (spongeWith c 136 544)
      (.seq (.seq (.block [.subImm .x .x9 .x27 2]) (.ite (.zero .x .x9) (rbLoop 2) (rbLoop 4)))
        (.block (retZ ++ epi))))

def rejBounded := rejBoundedWith .scalar

end VG.Impl.MlDsa.AArch64.Sample

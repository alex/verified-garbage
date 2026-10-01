import VerifiedGarbage.Impl.Ed25519.AArch64.Word

/-! The shared addition chain for inversion and square-root recovery. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def Z2 : Nat := 128
def T0 : Nat := 512
def T1 : Nat := 544
def T2 : Nat := 576
def T3 : Nat := 608

def sqn (o a n : Nat) : Prog isa :=
  .seq (.block (fieldSqr o a ++ const64 .x19 (BitVec.ofNat 64 (n - 1))))
    (.loop (.block (fieldSqr o o ++ [.subImm .x .x19 .x19 1])) (.nonzero .x .x19))

/-- From z in Z2, leave z^(2^250 - 1) in T1 and z^11 in T0. -/
def power250 : Prog isa :=
  .seq (.block (fieldSqr T0 Z2)) <|
  .seq (.block (fieldSqr T1 T0 ++ fieldSqr T1 T1)) <|
  .seq (.block (fieldMul T1 Z2 T1 ++ fieldMul T0 T0 T1 ++
    fieldSqr T2 T0 ++ fieldMul T1 T1 T2)) <|
  .seq (sqn T2 T1 5) <| .seq (.block (fieldMul T1 T2 T1)) <|
  .seq (sqn T2 T1 10) <| .seq (.block (fieldMul T2 T2 T1)) <|
  .seq (sqn T3 T2 20) <| .seq (.block (fieldMul T2 T3 T2)) <|
  .seq (sqn T2 T2 10) <| .seq (.block (fieldMul T1 T2 T1)) <|
  .seq (sqn T2 T1 50) <| .seq (.block (fieldMul T2 T2 T1)) <|
  .seq (sqn T3 T2 100) <| .seq (.block (fieldMul T2 T3 T2)) <|
  .seq (sqn T2 T2 50) (.block (fieldMul T1 T2 T1))

def invert : Prog isa := .seq power250 (.seq (sqn T1 T1 5) (.block (fieldMul T1 T1 T0)))

def rootPower : Prog isa := .seq power250 (.seq (sqn T1 T1 2) (.block (fieldMul T1 T1 Z2)))

end VG.Impl.Ed25519.AArch64

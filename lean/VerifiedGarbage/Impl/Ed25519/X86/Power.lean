import VerifiedGarbage.Impl.X25519.X86

/-! The shared addition chain for inversion and square-root recovery. -/
namespace VG.Impl.Ed25519.X86
open VG.X86
open VG.Impl.X25519.X86 (mul)

def Z2 : Nat := 128
def T0 : Nat := 512
def T1 : Nat := 544
def T2 : Nat := 576
def T3 : Nat := 608

def sqn (o a n : Nat) : Prog isa :=
  .seq (.block (mul o a a ++ [.mov .esi (.imm (BitVec.ofNat 32 (n - 1)))]))
    (.loop (.block (mul o o o ++ [.alu .sub .esi (.imm 1)])) .ne)

/-- From z in Z2, leave z^(2^250 - 1) in T1 and z^11 in T0. -/
def power250 : Prog isa :=
  .seq (.block (mul T0 Z2 Z2)) <|
  .seq (.block (mul T1 T0 T0 ++ mul T1 T1 T1)) <|
  .seq (.block (mul T1 Z2 T1 ++ mul T0 T0 T1 ++
    mul T2 T0 T0 ++ mul T1 T1 T2)) <|
  .seq (sqn T2 T1 5) <| .seq (.block (mul T1 T2 T1)) <|
  .seq (sqn T2 T1 10) <| .seq (.block (mul T2 T2 T1)) <|
  .seq (sqn T3 T2 20) <| .seq (.block (mul T2 T3 T2)) <|
  .seq (sqn T2 T2 10) <| .seq (.block (mul T1 T2 T1)) <|
  .seq (sqn T2 T1 50) <| .seq (.block (mul T2 T2 T1)) <|
  .seq (sqn T3 T2 100) <| .seq (.block (mul T2 T3 T2)) <|
  .seq (sqn T2 T2 50) (.block (mul T1 T2 T1))

def invert : Prog isa := .seq power250 (.seq (sqn T1 T1 5) (.block (mul T1 T1 T0)))

def rootPower : Prog isa := .seq power250 (.seq (sqn T1 T1 2) (.block (mul T1 T1 Z2)))

end VG.Impl.Ed25519.X86

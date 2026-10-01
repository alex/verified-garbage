import VerifiedGarbage.Impl.Ed25519.Arm.Field

/-! A fixed addition chain shared by inversion and square-root recovery. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def mulP (o a b : Slot) : Prog isa := mul (offset o) (offset a) (offset b)

def sqn (o a : Slot) (n : Nat) : Prog isa :=
  .seq (mulP o a a) <|
  .seq (.block [.movw .r10 (BitVec.ofNat 16 (n - 1))]) <|
    .loop (.seq (mulP o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne

/-- From z in slot 2, leave z^(2^250 - 1) in slot 15 and z^11 in slot 14. -/
def power250 : Prog isa :=
  .seq (mulP 14 2 2) <|
  .seq (mulP 15 14 14) <| .seq (mulP 15 15 15) <|
  .seq (mulP 15 2 15) <| .seq (mulP 14 14 15) <|
  .seq (mulP 16 14 14) <| .seq (mulP 15 15 16) <|
  .seq (sqn 16 15 5) <| .seq (mulP 15 16 15) <|
  .seq (sqn 16 15 10) <| .seq (mulP 16 16 15) <|
  .seq (sqn 17 16 20) <| .seq (mulP 16 17 16) <|
  .seq (sqn 16 16 10) <| .seq (mulP 15 16 15) <|
  .seq (sqn 16 15 50) <| .seq (mulP 16 16 15) <|
  .seq (sqn 17 16 100) <| .seq (mulP 16 17 16) <|
  .seq (sqn 16 16 50) (mulP 15 16 15)

def invert : Prog isa := .seq power250 (.seq (sqn 15 15 5) (mulP 15 15 14))

def rootPower : Prog isa := .seq power250 (.seq (sqn 15 15 2) (mulP 15 15 2))

end VG.Impl.Ed25519.Arm

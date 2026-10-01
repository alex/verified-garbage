import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.TCB.Arm.Isa

namespace VG.Impl.TripleDes.Arm
open VG.Arm

def rr (d n : Reg) : Instr := .mov d (.reg n)
def imm (d : Reg) (n : Nat) : Instr := .mov d (.imm (BitVec.ofNat 32 n))
def shr (r : Reg) (n : Nat) : List Instr :=
  if n = 0 then [] else [.mov r (.shifted r .lsr n)]
def placeBit (r : Reg) (n : Nat) : List Instr :=
  if n = 0 then [] else [.mov r (.shifted r .ror (32 - n))]
def mask (r : Reg) (n : Nat) : List Instr :=
  [.mov r (.shifted r .lsl (32 - n)), .mov r (.shifted r .lsr (32 - n))]

/-- A fixed bit permutation across two words. Each split is the width of
its low word; unused high bits are zero. -/
def permuteCode {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit : Nat)
    (lo hi srcLo srcHi tmp bit : Reg) : List Instr :=
  [imm lo 0, imm hi 0, imm bit 1] ++ (List.range m).flatMap fun k =>
    let source := n - positions.getD k 1
    let output := m - 1 - k
    [rr tmp (if source < srcSplit then srcLo else srcHi)] ++
      shr tmp (if source < srcSplit then source else source - srcSplit) ++
      [.dp .and tmp tmp (.reg bit)] ++
      placeBit tmp (if output < dstSplit then output else output - dstSplit) ++
      [.dp .eor (if output < dstSplit then lo else hi)
        (if output < dstSplit then lo else hi) (.reg tmp)]
end VG.Impl.TripleDes.Arm

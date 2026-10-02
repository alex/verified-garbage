import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.TCB.X86.Isa

namespace VG.Impl.TripleDes.X86
open VG.X86

def memOp (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }
def rr (d s : Reg) : Instr := .mov d (.reg s)
def imm (d : Reg) (n : Nat) : Instr := .mov d (.imm (BitVec.ofNat 32 n))
def shr (r : Reg) (n : Nat) : List Instr :=
  if n = 0 then [] else [.shift .shr r n]
def placeBit (r : Reg) (n : Nat) : List Instr :=
  if n = 0 then [] else [.shift .ror r (32 - n)]

/-- Fixed bit permutation across two 32-bit words. Each split is the width
of the low word; all other bits of each output are cleared. -/
def permuteCode {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit : Nat)
    (lo hi srcLo srcHi tmp : Reg) : List Instr :=
  [imm lo 0, imm hi 0] ++ (List.range m).flatMap fun k =>
    let source := n - positions.getD k 1
    let output := m - 1 - k
    [rr tmp (if source < srcSplit then srcLo else srcHi)] ++
      shr tmp (if source < srcSplit then source else source - srcSplit) ++
      ([.alu .and tmp (.imm 1)] : List Instr) ++
      placeBit tmp (if output < dstSplit then output else output - dstSplit) ++
      ([.alu .xor (if output < dstSplit then lo else hi) (.reg tmp)] : List Instr)

end VG.Impl.TripleDes.X86

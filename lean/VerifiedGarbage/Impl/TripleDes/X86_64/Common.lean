import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.TCB.X86_64.Isa

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64

def memOp (base : Reg) (offset : Nat) : MemOp := { base, disp := Int.ofNat offset }
def rr (d s : Reg) : Instr := .mov d (.reg s)
def imm (d : Reg) (n : Nat) : Instr := .mov d (.imm (BitVec.ofNat 32 n))

def shr (r : Reg) (n : Nat) : List Instr := if n = 0 then [] else [.shift .shr r n]
/-- A left shift of an isolated bit, using a rotate on its zero-filled word. -/
def placeBit (r : Reg) (n : Nat) : List Instr :=
  if n = 0 then [] else [.shift .ror r (64 - n)]

/-- Fixed FIPS permutation. Source and temporary are distinct from output.
Every address and instruction is independent of the input word. -/
def permuteCode {m : Nat} (positions : Vector Nat m) (n : Nat)
    (dst src tmp : Reg) : List Instr :=
  [imm dst 0] ++ (List.range m).flatMap fun i =>
    [rr tmp src] ++ shr tmp (n - positions.getD i 1) ++
      ([.alu .and tmp (.imm 1)] : List Instr) ++ placeBit tmp (m - 1 - i) ++
      ([.alu .or dst (.reg tmp)] : List Instr)

end VG.Impl.TripleDes.X86_64

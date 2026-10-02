import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.TCB.AArch64.Isa

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

def rr (d n : Reg) : Instr := .addImm .x d n 0

def imm (r : Reg) (n : Nat) : Instr := .movz .x r (BitVec.ofNat 16 n) 0

def shr (r : Reg) (n : Nat) : List Instr := if n = 0 then [] else [.lsr .x r r n]

def placeBit (r : Reg) (n : Nat) : List Instr := if n = 0 then [] else [.ror .x r r (64 - n)]

/-- Keep exactly the low `n` bits with two fixed shifts. -/
def mask (r : Reg) (n : Nat) : List Instr :=
  [.lsl .x r r (64 - n), .lsr .x r r (64 - n)]

def permuteCode {m : Nat} (positions : Vector Nat m) (n : Nat) (dst src tmp bit : Reg) : List Instr :=
  [imm dst 0, imm bit 1] ++ (List.range m).flatMap fun j =>
    [rr tmp src] ++ shr tmp (n - positions.getD j 1) ++
      [.logic .and .x tmp tmp bit] ++ placeBit tmp (m - 1 - j) ++
      [.logic .eor .x dst dst tmp]

end VG.Impl.TripleDes.AArch64

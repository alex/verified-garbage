import VerifiedGarbage.Impl.TripleDes.Circuit
import VerifiedGarbage.Impl.Aes.X86.Alloc

/-! Scalar DES Boolean circuits on IA-32. EBP is the scratch base;
ESI/EDI retain the Feistel halves. Inputs and outputs occupy fixed slots
16–21, with spills in slots 22–111. No address depends on a secret. -/
namespace VG.Impl.TripleDes.X86
open VG.X86

def sboxIns : List (Nat × Nat) := (List.range 6).map fun j => (j, 16 + j)
def sboxOuts (i : Nat) : List (Nat × Nat) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, 16 + j)
def sboxCode (i : Nat) : List Instr :=
  VG.Impl.Aes.X86.compile .ebp (Circuit.gates i) sboxIns (sboxOuts i)
    [.eax, .ebx, .ecx, .edx] (List.range' 22 90)
def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)
end VG.Impl.TripleDes.X86

import VerifiedGarbage.Impl.TripleDes.Circuit
import VerifiedGarbage.Impl.Aes.X86_64.Alloc

/-!
# Constant-time scalar DES S-boxes on x86-64

Six input planes are in `q 0 … q 5`; the four output planes are returned
in `q 0 … q 3`. These are general-purpose registers, so this is scalar
code. It computes the S-box independently at all 64 bit positions. Scratch
slots 8–55 are fixed spill locations; slots 0–7 are reserved for the block
function's saved registers and intermediate state. Left and right Feistel
halves (`r12`, `r13`) and argument pointers are preserved.
-/

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64

def q : Nat → Reg
  | 0 => .rax | 1 => .rcx | 2 => .r8 | 3 => .r9 | 4 => .r10 | _ => .r11

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)
def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, q j)

def sboxCode (i : Nat) : List Instr :=
  VG.Impl.Aes.X86_64.compile .rdx (Circuit.gates i) sboxIns (sboxOuts i)
    [.rbx, .rbp, .r14, .r15] 8 (List.range' 9 47)

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.X86_64

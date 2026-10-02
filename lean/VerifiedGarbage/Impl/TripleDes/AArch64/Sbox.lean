import VerifiedGarbage.Impl.TripleDes.Circuit
import VerifiedGarbage.Impl.Aes.AArch64.Alloc

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

def q : Nat → Reg
  | 0 => .x3 | 1 => .x4 | 2 => .x5 | 3 => .x6 | 4 => .x7 | _ => .x8

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)

def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Circuit.outputs i).getD j 0, q j)

/-- Six input planes and eight temporary registers; scratch slots 0–3 are reserved. -/
def sboxCode (i : Nat) : List Instr :=
  VG.Impl.Aes.AArch64.compile .x2 (Circuit.gates i) sboxIns (sboxOuts i)
    [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] .x9 (List.range' 4 48)

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.AArch64

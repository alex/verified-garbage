import VerifiedGarbage.Impl.Aes.X86.Alloc

/-!
# The bitsliced AES S-box on x86 (32-bit)

The circuit `Circuit.sbox` on the eight words of the bitsliced state
(slot `j` of the scratch buffer at `edi` holds bit `j` of 32 bytes), in
place, with `eax`, `ebx`, `ecx`, `edx` and `ebp` and spilling to the slots
from 8 on: the code that `compile` allocates for it. It is written out (and
`#guard` checks that it is what `compile` produces) so that the kernel,
which evaluates the code in the proofs, does not have to run the allocator.
-/

namespace VG.Impl.Aes.X86

open VG.X86 VG.Impl.Aes.Circuit

/-- The scratch buffer's base. -/
def sb : Reg := .edi

/-- The registers the layers may use. -/
def tmpRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

/-- The slots the S-box spills to. -/
def spillSlots : List Nat := List.range' 8 56

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in slot `7 - i`. -/
def sboxIns : List (Nat × Nat) := (List.range 8).map fun i => (x i, 7 - i)
def sboxOuts : List (Nat × Nat) := (List.range 8).map fun i => (s i, 7 - i)

/-! Short forms of the instructions, on slots of `sb`. -/
def movR (d s : Reg) : Instr := .mov d (.reg s)
def movS (d : Reg) (k : Nat) : Instr := .mov d (.mem (slotAt sb k))
def xorR (d s : Reg) : Instr := .alu .xor d (.reg s)
def xorS (d : Reg) (k : Nat) : Instr := .alu .xor d (.mem (slotAt sb k))
def andR (d s : Reg) : Instr := .alu .and d (.reg s)
def andS (d : Reg) (k : Nat) : Instr := .alu .and d (.mem (slotAt sb k))
def notR (d : Reg) : Instr := .alu .xor d (.imm (BitVec.allOnes 32))
def st (k : Nat) (r : Reg) : Instr := .store (slotAt sb k) r

/-- The S-box on the state in slots `0 … 7`, in place. -/
def sboxCode : List Instr := [
  movS .eax 4, xorS .eax 2, movS .ebx 7, xorS .ebx 1, movS .ecx 7, xorS .ecx 4, movS .edx 7,
  xorS .edx 2, movS .ebp 6, xorS .ebp 5, st 8 .ecx, movR .ecx .ebp, xorS .ecx 0, st 9 .ebp,
  movR .ebp .ecx, xorS .ebp 4, st 10 .ebp, movR .ebp .ebx, xorR .ebp .eax, st 11 .eax, movR
  .eax .ecx, xorS .eax 7, st 12 .eax, movR .eax .ecx, xorS .eax 1, st 13 .ecx, movR .ecx .eax,
  xorR .ecx .edx, st 14 .eax, movS .eax 3, xorR .eax .ebp, st 15 .ecx, movR .ecx .eax, xorS
  .ecx 2, xorS .eax 6, st 16 .ebp, movR .ebp .ecx, xorS .ebp 0, st 17 .ebp, movR .ebp .ecx,
  xorS .ebp 9, st 18 .ecx, movR .ecx .eax, xorS .ecx 8, st 19 .eax, movS .eax 0, xorR .eax
  .ecx, st 20 .eax, movR .eax .ebp, xorR .eax .ecx, st 21 .eax, movR .eax .ebp, xorR .eax .edx,
  st 22 .eax, movS .eax 9, xorR .eax .ecx, st 9 .ebp, movR .ebp .ebx, xorR .ebp .eax, st 23
  .ebp, movS .ebp 7, xorR .ebp .eax, st 24 .ebp, movS .ebp 16, andS .ebp 18, st 25 .edx, movS
  .edx 15, andS .edx 17, xorR .edx .ebp, st 26 .edx, movS .edx 10, andS .edx 0, xorR .edx .ebp,
  movR .ebp .ebx, andR .ebp .eax, st 27 .ebx, movS .ebx 14, andS .ebx 13, xorR .ebx .ebp, st 28
  .eax, movS .eax 12, andS .eax 20, xorR .eax .ebp, movS .ebp 8, andR .ebp .ecx, st 29 .ecx,
  movS .ecx 11, andS .ecx 21, xorR .ecx .ebp, st 30 .eax, movS .eax 25, andS .eax 9, xorR .eax
  .ebp, movS .ebp 26, xorR .ebp .ecx, xorR .edx .eax, xorR .ebx .ecx, xorS .eax 30, xorS .ebp
  19, xorS .edx 22, xorS .ebx 23, xorS .eax 24, movR .ecx .ebp, xorR .ecx .edx, andR .ebp .ebx,
  st 24 .ebx, movR .ebx .eax, xorR .ebx .ebp, st 23 .ebp, movR .ebp .ecx, andR .ebp .ebx, xorR
  .ebp .edx, st 22 .ecx, movS .ecx 24, xorR .ecx .eax, xorS .edx 23, andR .edx .ecx, xorR .edx
  .eax, movS .ecx 24, xorR .ecx .edx, st 24 .ebp, movR .ebp .ebx, xorR .ebp .edx, andR .eax
  .ebp, xorR .ecx .eax, xorR .ebx .eax, andS .ebx 24, xorS .ebx 22, movR .eax .ebx, xorR .eax
  .ecx, movS .ebp 24, xorR .ebp .edx, st 22 .ebp, movS .ebp 24, xorR .ebp .ebx, st 23 .ebx,
  movR .ebx .edx, xorR .ebx .ecx, st 19 .ebp, movS .ebp 22, xorR .ebp .eax, st 30 .eax, movR
  .eax .ebx, andS .eax 18, st 18 .eax, movR .eax .ecx, andS .eax 17, st 17 .eax, movR .eax
  .edx, andS .eax 0, st 26 .eax, movS .eax 19, andS .eax 28, st 28 .eax, movS .eax 23, andS
  .eax 13, st 13 .eax, movS .eax 24, andS .eax 20, st 20 .eax, movS .eax 22, andS .eax 29, st
  29 .eax, movR .eax .ebp, andS .eax 21, st 21 .eax, movS .eax 30, andS .eax 9, andS .ebx 16,
  andS .ecx 15, andS .edx 10, st 10 .eax, movS .eax 19, andS .eax 27, st 27 .eax, movS .eax 23,
  andS .eax 14, st 14 .ebx, movS .ebx 24, andS .ebx 12, st 12 .ebx, movS .ebx 22, andS .ebx 8,
  andS .ebp 11, st 11 .eax, movS .eax 30, andS .eax 25, xorR .ebx .ebp, xorR .edx .ecx, st 25
  .edx, movS .edx 20, xorS .edx 11, xorS .ecx 14, st 14 .ecx, movS .ecx 26, xorS .ecx 27, st 11
  .ebx, movS .ebx 26, xorS .ebx 20, st 20 .ebx, movS .ebx 21, xorS .ebx 10, st 10 .ebx, movS
  .ebx 18, xorS .ebx 28, st 18 .ebx, movS .ebx 29, xorS .ebx 21, xorR .ebp .eax, movS .eax 27,
  xorR .eax .edx, xorS .ecx 18, st 27 .ebp, movS .ebp 13, xorS .ebp 11, xorS .ebx 28, st 28
  .edx, movS .edx 11, xorR .edx .ecx, xorS .ecx 12, st 12 .edx, movS .edx 10, xorR .edx .ebp,
  xorS .ebp 14, st 14 .eax, movS .eax 13, xorR .eax .ebx, xorR .ecx .edx, st 13 .ecx, movS .ecx
  17, xorR .ecx .ebp, xorR .ebx .ebp, xorS .edx 14, notR .edx, movS .ebp 28, xorS .ebp 12, notR
  .ebp, st 12 .ebp, movR .ebp .eax, xorS .ebp 13, st 28 .edx, movS .edx 18, xorR .edx .ecx,
  xorS .ecx 20, st 20 .ecx, movS .ecx 25, xorS .ecx 13, xorR .eax .edx, notR .eax, xorS .ebp
  27, notR .ebp, st 7 .ebx, st 6 .eax, st 5 .ebp, st 4 .edx, st 2 .ecx, movS .eax 20, st 3
  .eax, movS .eax 28, st 1 .eax, movS .eax 12, st 0 .eax]

#guard sboxCode == compile sb sbox sboxIns sboxOuts tmpRegs spillSlots

end VG.Impl.Aes.X86

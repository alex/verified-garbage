import VerifiedGarbage.Impl.Aes.X86_64.Alloc

/-!
# The bitsliced AES S-box on x86-64

The circuit `Circuit.sbox` on the eight words of the bitsliced state
(`q j` holds bit `j` of 64 bytes), in place, spilling to the first slots
of the scratch buffer at `r9`: the code that `compile` allocates for it.
It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64 VG.Impl.Aes.Circuit

/-- The registers of the bitsliced state: word `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .rax | 1 => .rbx | 2 => .rcx | 3 => .rbp
  | 4 => .r10 | 5 => .r11 | 6 => .r12 | _ => .r13

/-- The two temporaries of the round. -/
def t0 : Reg := .r14
def t1 : Reg := .r15

/-- The scratch buffer's base. -/
def sb : Reg := .r9

/-- The slot of all ones, and the slots the S-box spills to. -/
def onesSlot : Nat := 0
def spillSlots : List Nat := List.range' 1 47

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q (7 - i))

/-! Short forms of the instructions, on slots of `sb`. -/
def movR (d s : Reg) : Instr := .mov d (.reg s)
def movS (d : Reg) (k : Nat) : Instr := .mov d (.mem (slotAt sb k))
def xorR (d s : Reg) : Instr := .alu .xor d (.reg s)
def xorS (d : Reg) (k : Nat) : Instr := .alu .xor d (.mem (slotAt sb k))
def andR (d s : Reg) : Instr := .alu .and d (.reg s)
def andS (d : Reg) (k : Nat) : Instr := .alu .and d (.mem (slotAt sb k))
def st (k : Nat) (r : Reg) : Instr := .store (slotAt sb k) r
def ones (d : Reg) : Instr := .movImm64 d (BitVec.allOnes 64)

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  ones .r14, st 0 .r14, movR .r14 .r10, xorR .r14 .rcx, movR .r15 .r13, xorR .r15 .rbx,
  st 1 .rbp, movR .rbp .r13, xorR .rbp .r10, st 2 .rbp, movR .rbp .r13, xorR .rbp .rcx,
  xorR .r11 .r12, st 3 .r12, movR .r12 .r11, xorR .r12 .rax, xorR .r10 .r12, st 4 .r10,
  movR .r10 .r15, xorR .r10 .r14, st 5 .r14, movR .r14 .r12, xorR .r14 .r13, xorR .rbx .r12,
  st 6 .r14, movR .r14 .rbx, xorR .r14 .rbp, st 7 .rbx, movS .rbx 1, xorR .rbx .r10,
  xorR .rcx .rbx, xorS .rbx 3, st 3 .r12, movR .r12 .rcx, xorR .r12 .rax, st 1 .r12,
  movR .r12 .rcx, xorR .r12 .r11, st 8 .r14, movR .r14 .rbx, xorS .r14 2, st 9 .rbx,
  movR .rbx .rax, xorR .rbx .r14, st 10 .rbx, movR .rbx .r12, xorR .rbx .r14, st 11 .rbx,
  movR .rbx .r12, xorR .rbx .rbp, xorR .r11 .r14, st 12 .rbx, movR .rbx .r15, xorR .rbx .r11,
  xorR .r13 .r11, st 13 .r13, movR .r13 .r10, andR .r13 .rcx, st 14 .r10, movS .r10 8,
  andS .r10 1, xorR .r10 .r13, st 15 .rcx, movS .rcx 4, andR .rcx .rax, xorR .rcx .r13,
  movR .r13 .r15, andR .r13 .r11, st 16 .r15, movS .r15 7, andS .r15 3, xorR .r15 .r13,
  st 17 .r11, movS .r11 6, andS .r11 10, xorR .r11 .r13, movS .r13 2, andR .r13 .r14,
  st 18 .r14, movS .r14 5, andS .r14 11, xorR .r14 .r13, st 19 .rax, movR .rax .rbp,
  andR .rax .r12, xorR .rax .r13, xorR .r10 .r14, xorR .rcx .rax, xorR .r15 .r14, xorR .r11 .rax,
  xorS .r10 9, xorS .rcx 12, xorR .r15 .rbx, xorS .r11 13, movR .rbx .r10, xorR .rbx .rcx,
  andR .r10 .r15, movR .rax .r11, xorR .rax .r10, movR .r14 .rbx, andR .r14 .rax, xorR .r14 .rcx,
  movR .r13 .r15, xorR .r13 .r11, xorR .rcx .r10, andR .rcx .r13, xorR .rcx .r11, xorR .r15 .rcx,
  movR .r13 .rax, xorR .r13 .rcx, andR .r11 .r13, xorR .r15 .r11, xorR .rax .r11, andR .rax .r14,
  xorR .rbx .rax, movR .rax .rbx, xorR .rax .r15, movR .r11 .r14, xorR .r11 .rcx, movR .r13 .r14,
  xorR .r13 .rbx, movR .r10 .rcx, xorR .r10 .r15, st 13 .rbp, movR .rbp .r11, xorR .rbp .rax,
  st 12 .rax, movR .rax .r10, andS .rax 15, st 15 .rax, movR .rax .r15, andS .rax 1,
  st 1 .rax, movR .rax .rcx, andS .rax 19, st 19 .rax, movR .rax .r13, andS .rax 17,
  st 17 .rax, movR .rax .rbx, andS .rax 3, st 3 .rax, movR .rax .r14, andS .rax 10,
  st 10 .rax, movR .rax .r11, andS .rax 18, st 18 .rax, movR .rax .rbp, andS .rax 11,
  andS .r12 12, andS .r10 14, andS .r15 8, andS .rcx 4, andS .r13 16, andS .rbx 7,
  andS .r14 6, andS .r11 2, andS .rbp 5, st 5 .r14, movS .r14 12, andS .r14 13,
  xorR .r11 .rbp, xorR .rcx .r15, xorS .rbx 10, xorR .r10 .r15, movS .r15 19, xorR .r15 .r13,
  st 13 .rcx, movS .rcx 19, xorS .rcx 10, xorR .r12 .rax, st 10 .rcx, movS .rcx 15,
  xorS .rcx 17, xorS .rax 18, xorR .rbp .r14, xorR .r13 .rbx, xorR .r15 .rcx, movS .r14 3,
  xorR .r14 .r11, xorS .rax 17, xorR .r11 .r15, xorS .r15 5, xorR .r12 .r14, xorR .r10 .r14,
  movS .r14 3, xorR .r14 .rax, xorR .r15 .r12, st 3 .rbp, movS .rbp 1, xorR .rbp .r10,
  xorR .rax .r10, xorR .r13 .r12, xorS .r13 0, xorR .rbx .r11, xorS .rbx 0, movR .r11 .r14,
  xorR .r11 .r15, xorR .rcx .rbp, xorS .rbp 10, xorS .r15 13, xorR .r14 .rcx, xorS .r14 0,
  xorS .r11 3, xorS .r11 0, st 3 .r13, movR .r13 .rax, movR .r12 .r14, movR .r10 .rcx,
  movR .rcx .r15, st 13 .rbx, movS .rbx 3, movS .rax 13]

#guard sboxCode == compile sb sbox sboxIns sboxOuts [t0, t1] onesSlot spillSlots

end VG.Impl.Aes.X86_64

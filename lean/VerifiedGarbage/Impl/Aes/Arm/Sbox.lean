import VerifiedGarbage.Impl.Aes.Arm.Alloc

/-!
# The bitsliced AES S-box on ARMv7

The circuit `Circuit.sbox` on the eight words of the bitsliced state
(`q j` holds bit `j` of 32 bytes: two blocks), in place, with the
temporaries in `r10`–`r12` and `lr`, all ones in slot 0 of the scratch
buffer at `r8`, and spilling to its next slots: the code that `compile`
allocates for it. It is written out (and `#guard` checks that it is what
`compile` produces) so that the kernel, which evaluates the code in the
proofs, does not have to run the allocator.
-/

namespace VG.Impl.Aes.Arm

open VG.Arm VG.Impl.Aes.Circuit

/-- The registers of the bitsliced state: word `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .r0 | 1 => .r1 | 2 => .r2 | 3 => .r3
  | 4 => .r4 | 5 => .r5 | 6 => .r6 | _ => .r7

/-- The scratch buffer's base. -/
def sb : Reg := .r8

/-- The registers the S-box may use for its temporaries. -/
def sboxFree : List Reg := [.r10, .r11, .r12, .lr]

/-- The slot of all ones, the variables `splitXnor` adds, and the slots the
S-box may spill to. -/
def onesSlot : Nat := 0
def onesVar : Nat := 124
def freshVar : Nat := 125
def spillSlots : List Nat := List.range' 1 31

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q (7 - i))

/-! Short forms of the instructions, on slots of `sb`. -/
def movR (d n : Reg) : Instr := .mov d (.reg n)
def eorR (d n m : Reg) : Instr := .dp .eor d n (.reg m)
def andR (d n m : Reg) : Instr := .dp .and d n (.reg m)
def ldS (d : Reg) (k : Nat) : Instr := .ldr d sb (4 * k)
def stS (k : Nat) (r : Reg) : Instr := .str r sb (4 * k)

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .mov .r10 (.imm 0), .dp .sub .r10 .r10 (.imm 1), stS onesSlot .r10,
  eorR .r10 .r4 .r2, eorR .r11 .r7 .r1, eorR .r12 .r7 .r4, eorR .lr .r7 .r2, eorR .r5 .r6 .r5,
  stS 1 .r12, eorR .r12 .r5 .r0, eorR .r4 .r12 .r4, stS 2 .r4, eorR .r4 .r11 .r10, stS 3 .r10,
  eorR .r10 .r12 .r7, eorR .r1 .r12 .r1, stS 4 .r10, eorR .r10 .r1 .lr, eorR .r3 .r3 .r4, eorR
  .r2 .r3 .r2, eorR .r3 .r3 .r6, eorR .r6 .r2 .r0, stS 5 .r1, eorR .r1 .r2 .r5, stS 6 .r12, ldS
  .r12 1, stS 7 .r6, eorR .r6 .r3 .r12, stS 8 .r3, eorR .r3 .r0 .r6, eorR .r12 .r1 .r6, stS 9
  .r12, eorR .r12 .r1 .lr, eorR .r5 .r5 .r6, stS 10 .r12, eorR .r12 .r11 .r5, eorR .r7 .r7 .r5,
  stS 11 .r7, andR .r7 .r4 .r2, stS 12 .r4, ldS .r4 7, stS 13 .r2, andR .r2 .r10 .r4, eorR .r2
  .r2 .r7, stS 14 .r10, ldS .r10 2, andR .r4 .r10 .r0, eorR .r4 .r4 .r7, andR .r7 .r11 .r5, stS
  15 .r11, ldS .r11 5, ldS .r10 6, stS 16 .r5, andR .r5 .r11 .r10, eorR .r5 .r5 .r7, ldS .r11
  4, andR .r10 .r11 .r3, eorR .r10 .r10 .r7, ldS .r7 1, andR .r11 .r7 .r6, ldS .r7 3, stS 17
  .r6, ldS .r6 9, stS 18 .r3, andR .r3 .r7 .r6, eorR .r3 .r3 .r11, andR .r7 .lr .r1, eorR .r7
  .r7 .r11, eorR .r2 .r2 .r3, eorR .r4 .r4 .r7, eorR .r5 .r5 .r3, eorR .r10 .r10 .r7, ldS .r7
  8, eorR .r2 .r2 .r7, ldS .r7 10, eorR .r4 .r4 .r7, eorR .r5 .r5 .r12, ldS .r12 11, eorR .r10
  .r10 .r12, eorR .r12 .r2 .r4, andR .r2 .r2 .r5, eorR .r7 .r10 .r2, andR .r3 .r12 .r7, eorR
  .r3 .r3 .r4, eorR .r11 .r5 .r10, eorR .r4 .r4 .r2, andR .r4 .r4 .r11, eorR .r4 .r4 .r10, eorR
  .r5 .r5 .r4, eorR .r11 .r7 .r4, andR .r10 .r10 .r11, eorR .r5 .r10 .r5, eorR .r7 .r7 .r10,
  andR .r7 .r3 .r7, eorR .r12 .r12 .r7, eorR .r7 .r12 .r5, eorR .r10 .r3 .r4, eorR .r11 .r3
  .r12, eorR .r2 .r4 .r5, stS 11 .lr, eorR .lr .r10 .r7, stS 10 .r7, ldS .r7 13, andR .r7 .r2
  .r7, stS 13 .r7, ldS .r7 7, andR .r7 .r5 .r7, andR .r0 .r4 .r0, stS 7 .r7, ldS .r7 16, andR
  .r7 .r11 .r7, stS 16 .r7, ldS .r7 6, andR .r7 .r12 .r7, stS 6 .r7, ldS .r7 18, andR .r7 .r3
  .r7, stS 18 .r0, ldS .r0 17, andR .r0 .r10 .r0, andR .r6 .lr .r6, stS 9 .r0, ldS .r0 10, andR
  .r1 .r0 .r1, stS 17 .r1, ldS .r1 12, andR .r2 .r2 .r1, ldS .r1 14, andR .r5 .r5 .r1, ldS .r1
  2, andR .r4 .r4 .r1, ldS .r1 15, andR .r11 .r11 .r1, ldS .r1 5, andR .r12 .r12 .r1, ldS .r1
  4, andR .r3 .r3 .r1, ldS .r1 1, andR .r10 .r10 .r1, ldS .r1 3, andR .lr .lr .r1, ldS .r1 11,
  andR .r0 .r0 .r1, eorR .r10 .r10 .lr, eorR .r4 .r5 .r4, eorR .r12 .r7 .r12, eorR .r2 .r2 .r5,
  ldS .r5 18, eorR .r1 .r5 .r11, eorR .r5 .r5 .r7, ldS .r7 17, eorR .r7 .r6 .r7, stS 17 .r4,
  ldS .r4 13, stS 18 .r5, ldS .r5 16, eorR .r4 .r4 .r5, stS 13 .r2, ldS .r2 9, eorR .r2 .r2
  .r6, eorR .lr .lr .r0, eorR .r11 .r11 .r12, eorR .r1 .r1 .r4, ldS .r0 6, eorR .r6 .r0 .r10,
  eorR .r5 .r5 .r2, eorR .r10 .r10 .r1, eorR .r3 .r3 .r1, eorR .r7 .r7 .r6, ldS .r1 13, eorR
  .r1 .r1 .r6, eorR .r0 .r0 .r5, eorR .r3 .r3 .r7, ldS .r6 7, eorR .r6 .r6 .r1, eorR .r5 .r5
  .r1, eorR .r11 .r11 .r7, ldS .r7 0, eorR .r1 .r11 .r7, eorR .r12 .r12 .r10, eorR .r12 .r12
  .r7, eorR .r10 .r0 .r3, eorR .r4 .r4 .r6, ldS .r11 18, eorR .r11 .r11 .r6, ldS .r6 17, eorR
  .r2 .r6 .r3, eorR .r0 .r0 .r4, eorR .r6 .r0 .r7, eorR .lr .lr .r10, eorR .lr .lr .r7, movR
  .r7 .r5, movR .r5 .lr, movR .r3 .r11, movR .r0 .r12]

#guard sboxCode == compile sb sbox sboxIns sboxOuts sboxFree onesSlot onesVar freshVar spillSlots

end VG.Impl.Aes.Arm

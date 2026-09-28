import VerifiedGarbage.Impl.Aes.AArch64.Alloc

/-!
# The bitsliced AES S-box on AArch64

The circuit `Circuit.sbox` on the eight words of the bitsliced state
(`q j` holds bit `j` of 64 bytes), in place, with the temporaries in
`x14`–`x17` and `x19`–`x28`, all ones in `x29`, and spilling to the first
slots of the scratch buffer at `x5`: the code that `compile` allocates for
it. It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

namespace VG.Impl.Aes.AArch64

open VG.AArch64 VG.Impl.Aes.Circuit

/-- The registers of the bitsliced state: word `j` is in `q j`. -/
def q : Nat → Reg
  | 0 => .x6 | 1 => .x7 | 2 => .x8 | 3 => .x9
  | 4 => .x10 | 5 => .x11 | 6 => .x12 | _ => .x13

/-- The scratch buffer's base. -/
def sb : Reg := .x5

/-- The register of all ones during the S-box. -/
def ones : Reg := .x29

/-- The registers the S-box may use for its temporaries. -/
def sboxFree : List Reg :=
  [.x14, .x15, .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- The slots the S-box spills to. -/
def spillSlots : List Nat := List.range 48

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (s i, q (7 - i))

/-! Short forms of the instructions, on slots of `sb`. -/
def movR (d n : Reg) : Instr := .addImm .x d n 0
def eorR (d n m : Reg) : Instr := .logic .eor .x d n m
def andR (d n m : Reg) : Instr := .logic .and .x d n m
def orrR (d n m : Reg) : Instr := .logic .orr .x d n m
def ldS (d : Reg) (k : Nat) : Instr := .ldr .x d sb (8 * k)
def stS (k : Nat) (r : Reg) : Instr := .str .x r sb (8 * k)

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .movz .x ones 0 0, .subImm .x ones ones 1,
  eorR .x14 .x10 .x8, eorR .x15 .x13 .x7, eorR .x16 .x13 .x10, eorR .x17 .x13 .x8,
  eorR .x11 .x12 .x11, eorR .x19 .x11 .x6, eorR .x10 .x19 .x10, eorR .x20 .x15 .x14,
  eorR .x21 .x19 .x13, eorR .x7 .x19 .x7, eorR .x22 .x7 .x17, eorR .x9 .x9 .x20, eorR .x8 .x9 .x8,
  eorR .x9 .x9 .x12, eorR .x12 .x8 .x6, eorR .x23 .x8 .x11, eorR .x24 .x9 .x16, eorR .x25 .x6 .x24,
  eorR .x26 .x23 .x24, eorR .x27 .x23 .x17, eorR .x11 .x11 .x24, eorR .x28 .x15 .x11,
  eorR .x13 .x13 .x11, stS 0 .x13, andR .x13 .x20 .x8, stS 1 .x20, andR .x20 .x22 .x12,
  eorR .x20 .x20 .x13, stS 2 .x22, andR .x22 .x10 .x6, eorR .x22 .x22 .x13, andR .x13 .x15 .x11,
  stS 3 .x15, andR .x15 .x7 .x19, eorR .x15 .x15 .x13, stS 4 .x7, andR .x7 .x21 .x25,
  eorR .x7 .x7 .x13, andR .x13 .x16 .x24, stS 5 .x16, andR .x16 .x14 .x26, eorR .x16 .x16 .x13,
  stS 6 .x14, andR .x14 .x17 .x23, eorR .x14 .x14 .x13, eorR .x20 .x20 .x16, eorR .x22 .x22 .x14,
  eorR .x15 .x15 .x16, eorR .x7 .x7 .x14, eorR .x20 .x20 .x9, eorR .x22 .x22 .x27,
  eorR .x15 .x15 .x28, ldS .x28 0, eorR .x7 .x7 .x28, eorR .x28 .x20 .x22, andR .x20 .x20 .x15,
  eorR .x27 .x7 .x20, andR .x9 .x28 .x27, eorR .x9 .x9 .x22, eorR .x14 .x15 .x7,
  eorR .x22 .x22 .x20, andR .x22 .x22 .x14, eorR .x22 .x22 .x7, eorR .x15 .x15 .x22,
  eorR .x14 .x27 .x22, andR .x7 .x7 .x14, eorR .x15 .x7 .x15, eorR .x27 .x27 .x7,
  andR .x27 .x9 .x27, eorR .x28 .x28 .x27, eorR .x27 .x28 .x15, eorR .x7 .x9 .x22,
  eorR .x14 .x9 .x28, eorR .x20 .x22 .x15, eorR .x16 .x7 .x27, andR .x8 .x20 .x8,
  andR .x12 .x15 .x12, andR .x6 .x22 .x6, andR .x11 .x14 .x11, andR .x19 .x28 .x19,
  andR .x25 .x9 .x25, andR .x24 .x7 .x24, andR .x26 .x16 .x26, andR .x23 .x27 .x23, ldS .x13 1,
  andR .x20 .x20 .x13, ldS .x13 2, andR .x15 .x15 .x13, andR .x22 .x22 .x10, ldS .x10 3,
  andR .x14 .x14 .x10, ldS .x10 4, andR .x28 .x28 .x10, andR .x9 .x9 .x21, ldS .x21 5,
  andR .x7 .x7 .x21, ldS .x21 6, andR .x16 .x16 .x21, andR .x27 .x27 .x17, eorR .x7 .x7 .x16,
  eorR .x22 .x15 .x22, eorR .x28 .x25 .x28, eorR .x20 .x20 .x15, eorR .x15 .x6 .x14,
  eorR .x6 .x6 .x25, eorR .x23 .x26 .x23, eorR .x8 .x8 .x11, eorR .x24 .x24 .x26,
  eorR .x16 .x16 .x27, eorR .x14 .x14 .x28, eorR .x15 .x15 .x8, eorR .x27 .x19 .x7,
  eorR .x11 .x11 .x24, eorR .x7 .x7 .x15, eorR .x9 .x9 .x15, eorR .x23 .x23 .x27,
  eorR .x20 .x20 .x27, eorR .x19 .x19 .x11, eorR .x9 .x9 .x23, eorR .x12 .x12 .x20,
  eorR .x13 .x11 .x20, eorR .x14 .x14 .x23, eorR .x14 .x14 .x29, eorR .x28 .x28 .x7,
  eorR .x28 .x28 .x29, eorR .x7 .x19 .x9, eorR .x10 .x8 .x12, eorR .x6 .x6 .x12, eorR .x8 .x22 .x9,
  eorR .x12 .x19 .x10, eorR .x12 .x12 .x29, eorR .x11 .x16 .x7, eorR .x11 .x11 .x29, movR .x9 .x6,
  movR .x7 .x14, movR .x6 .x28]

#guard sboxCode == compile sb sbox sboxIns sboxOuts sboxFree ones spillSlots

end VG.Impl.Aes.AArch64

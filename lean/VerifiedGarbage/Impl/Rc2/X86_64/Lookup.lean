import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Constant-time RC2 selection on baseline x86-64

All candidates are visited in a fixed order. The secret index is compared
with each public candidate using arithmetic, never used as an address or
branch condition. Subtracting one from `x XOR i` borrows exactly when
`x = i`; `sbb r10, r10` turns that borrow into the selection mask.
-/

namespace VG.Impl.Rc2.X86_64

open VG.X86_64

def memOp (base : Reg) (offset : Nat) : MemOp := { base, disp := Int.ofNat offset }
def rr (dst src : Reg) : Instr := .mov dst (.reg src)
def imm (dst : Reg) (n : Nat) : Instr := .mov dst (.imm (BitVec.ofNat 32 n))

/-- With a byte in `rax`, the equality mask for candidate `i` in `r10`.
Leaves the input in `rax`. -/
def selectMask (i : Nat) : List Instr :=
  [rr .r10 .rax, .alu .xor .r10 (.imm (BitVec.ofNat 32 i)),
   .alu .sub .r10 (.imm 1), .alu .sbb .r10 (.reg .r10)]

/-- Accumulate PITABLE candidate `i` into `rcx`. -/
def piStep (i : Nat) : List Instr :=
  selectMask i ++
    ([.alu .and .r10 (.imm ((Spec.Rc2.piTable.getD i 0).setWidth 32)),
      .alu .or .rcx (.reg .r10)] : List Instr)

/-- PITABLE of the low byte of `rax`, returned in `rax`. Clobbers only
`rax`, `rcx`, `r10`, `r11`, and flags; accesses no memory. -/
def piLookup : List Instr :=
  [.alu .and .rax (.imm 255), imm .rcx 0] ++
    (List.range 256).flatMap piStep ++ [rr .rax .rcx]

/-- Load a little-endian 16-bit word at the public offset `2*i` of `rdi`
into `r8`. Byte loads avoid reading past the last schedule word. -/
def loadKey (i : Nat) : List Instr :=
  [.movzx8 .r8 (memOp .rdi (2 * i)), .movzx8 .r9 (memOp .rdi (2 * i + 1)),
   .shift .ror .r9 56, .alu .or .r8 (.reg .r9)]

/-- Accumulate schedule candidate `i` into `rcx`. -/
def keyStep (i : Nat) : List Instr :=
  selectMask i ++ loadKey i ++
    ([.alu .and .r8 (.reg .r10), .alu .or .rcx (.reg .r8)] : List Instr)

/-- Select schedule word `rax & 63`, returned in `rax`, from all 64 words
at `rdi`. Clobbers `rax`, `rcx`, `r8`–`r11`, and flags. -/
def keyLookup : List Instr :=
  [.alu .and .rax (.imm 63), imm .rcx 0] ++
    (List.range 64).flatMap keyStep ++ [rr .rax .rcx]

end VG.Impl.Rc2.X86_64

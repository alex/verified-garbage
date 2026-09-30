import VerifiedGarbage.Impl.X25519.X86_64

/-!
# Ed25519 scalar reduction on x86-64

Binary division by the constant subgroup order. Each input bit doubles the
four-word remainder, adds the bit, subtracts L, and selects the subtraction
exactly when there was no borrow. All 512 bits are processed, independent
of their values. The body uses integer multiplication by two (ADC), shifts,
and masks, with no division instruction or secret-dependent branch.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ zero4 saved)

def orderLo : BitVec 64 := 0x5812631a5cf5d3ed
def orderHi : BitVec 64 := 0x14def9dea2f79cd6
def orderTop : BitVec 64 := 0x1000000000000000

/-- Double the remainder and add bit j of the byte in rbp. SHR puts that
bit in CF, which the four ADC instructions propagate through the limbs. -/
def scalarShift (j : Nat) : List Instr :=
  [.mov .rcx (.reg .rbp), .shift .shr .rcx (j + 1),
    .alu .adc .r8 (.reg .r8), .alu .adc .r9 (.reg .r9),
    .alu .adc .r10 (.reg .r10), .alu .adc .r11 (.reg .r11)]

/-- Save the original remainder and subtract L. -/
def scalarSubtract : List Instr :=
  [.mov .r12 (.reg .r8), .mov .r13 (.reg .r9), .mov .r14 (.reg .r10), .mov .r15 (.reg .r11),
    .movImm64 .rcx orderLo, .alu .sub .r8 (.reg .rcx),
    .movImm64 .rcx orderHi, .alu .sbb .r9 (.reg .rcx), .alu .sbb .r10 (.imm 0),
    .movImm64 .rcx orderTop, .alu .sbb .r11 (.reg .rcx)]

/-- Select the original remainder on borrow, the subtraction otherwise. -/
def scalarSelect : List Instr :=
  [.alu .sbb .rax (.reg .rax)] ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (x, y) =>
    [.alu .xor y (.reg x), .alu .and y (.reg .rax), .alu .xor x (.reg y)])

def scalarBit (j : Nat) : List Instr := scalarShift j ++ scalarSubtract ++ scalarSelect

def scalarByte : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rbp { base := .rsi, index := some .rbx }] ++
    (List.range 8).reverse.flatMap scalarBit ++ [.alu .test .rbx (.reg .rbx)]

def scalarSave : List Instr := saved.map fun (r, d) => .store (at_ .rdx d) r
def scalarRestore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rdx d))

/-- `out = rdi`, the 64-byte input at rsi, scratch at rdx. -/
def scalarReduce : Prog isa :=
  .seq (.block (scalarSave ++ zero4 ++ [.mov32 .rbx (.imm 64)])) <|
  .seq (.loop (.block scalarByte) .ne) <|
    .block (scalarRestore ++ [.store (at_ .rdi 0) .r8, .store (at_ .rdi 8) .r9,
      .store (at_ .rdi 16) .r10, .store (at_ .rdi 24) .r11])

end VG.Impl.Ed25519.X86_64

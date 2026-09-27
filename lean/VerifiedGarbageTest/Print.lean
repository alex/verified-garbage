import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.TCB.Arm.Print

/-!
# Golden tests for the trusted printers

The printers are part of the TCB but not verified; these tests pin down their
output for every construct, so that changes to them are deliberate and show
up in review.
-/

namespace VG.Test

open X86_64

/-- Every `Code` constructor, nested. -/
def sample : Prog isa :=
  .seq (.block [.alu .xor .rax (.reg .rax)])
    (.ite .ne
      (.loop (.block [.alu .add .rax (.mem { base := .rdi, index := some .rcx, scale := 8, disp := -8 }),
                      .alu .sub .rcx (.imm 1)]) .ne)
      (.block [.store { base := .rsi, disp := 16 } .rax, .mov .rdx (.imm (-1))]))

#guard printer.function sample == [
  "xor rax, rax",
  "jne 20f",
  "mov QWORD PTR [rsi+16], rax",
  "mov rdx, -1",
  "jmp 21f",
  "20:",
  "22:",
  "add rax, QWORD PTR [rdi+rcx*8-8]",
  "sub rcx, 1",
  "jne 22b",
  "21:",
  "ret"
]

/-- Every 32-bit instruction form. -/
def sample32 : Prog isa := .block [
  .mov32 .rax (.reg .r8),
  .mov32 .r15 (.imm 0xfffffffe),
  .mov32 .rcx (.mem { base := .rsi, disp := 60 }),
  .store32 { base := .rdi, index := some .rdx, scale := 4 } .r11,
  .alu32 .add .rbp (.imm 0x428a2f98),
  .alu32 .xor .r12 (.reg .rsp),
  .alu32 .and .r13 (.mem { base := .rcx, disp := -4 }),
  .shift32 .ror .rbx 25,
  .shift32 .shr .r9 3,
  .bswap32 .r10
]

#guard printer.function sample32 == [
  "mov eax, r8d",
  "mov r15d, -2",
  "mov ecx, DWORD PTR [rsi+60]",
  "mov DWORD PTR [rdi+rdx*4], r11d",
  "add ebp, 1116352408",
  "xor r12d, esp",
  "and r13d, DWORD PTR [rcx-4]",
  "ror ebx, 25",
  "shr r9d, 3",
  "bswap r10d",
  "ret"
]

/-- The byte instructions, every 8-bit register name, and 64-bit `bswap`. -/
def sample8 : Prog isa := .block ([
  .movzx8 .rax (.mk .rsi (some .rcx) 1 32),
  .movzx8 .r15 { base := .r12 },
  .bswap .rax,
  .bswap .r9] ++
  [Reg.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].map (.store8 { base := .rdi, disp := -3 }))

#guard printer.function sample8 == [
  "movzx eax, BYTE PTR [rsi+rcx*1+32]",
  "movzx r15d, BYTE PTR [r12]",
  "bswap rax",
  "bswap r9",
  "mov BYTE PTR [rdi-3], al",
  "mov BYTE PTR [rdi-3], cl",
  "mov BYTE PTR [rdi-3], dl",
  "mov BYTE PTR [rdi-3], bl",
  "mov BYTE PTR [rdi-3], spl",
  "mov BYTE PTR [rdi-3], bpl",
  "mov BYTE PTR [rdi-3], sil",
  "mov BYTE PTR [rdi-3], dil",
  "mov BYTE PTR [rdi-3], r8b",
  "mov BYTE PTR [rdi-3], r9b",
  "mov BYTE PTR [rdi-3], r10b",
  "mov BYTE PTR [rdi-3], r11b",
  "mov BYTE PTR [rdi-3], r12b",
  "mov BYTE PTR [rdi-3], r13b",
  "mov BYTE PTR [rdi-3], r14b",
  "mov BYTE PTR [rdi-3], r15b",
  "ret"
]

/-- The 64-bit shifts and `movabs`, including an immediate ≥ 2⁶³. -/
def sample64 : Prog isa := .block [
  .shift .ror .rax 28,
  .shift .ror .r15 1,
  .shift .shr .rbx 63,
  .shift .shr .r9 7,
  .movImm64 .rcx 0x428a2f98d728ae22,
  .movImm64 .r13 0xb5c0fbcfec4d3b2f,
  .movImm64 .rsi 1
]

#guard printer.function sample64 == [
  "ror rax, 28",
  "ror r15, 1",
  "shr rbx, 63",
  "shr r9, 7",
  "movabs rcx, 4794697086780616226",
  "movabs r13, -5349999486874862801",
  "movabs rsi, 1",
  "ret"
]

/-- Every AArch64 instruction form, and both branch conditions. -/
def sampleA64 : Prog AArch64.isa :=
  .ite (.zero .x .x2) (.block [])
    (.loop (.block [
      .add .w .x4 .x5 .x6, .add .x .x0 .x1 .x30,
      .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1,
      .logic .and .w .x7 .x8 .x9, .logic .orr .w .x7 .x8 .x9, .logic .eor .x .x7 .x8 .x9,
      .ror .w .x13 .x8 25, .lsr .w .x14 .x15 10, .rev32 .x12 .x12,
      .movz .w .x13 0x2f98 0, .movk .w .x13 0x428a 1,
      .ldr .w .x12 .x1 60, .str .w .x12 .x3 4, .ldr .x .x16 .x17 8, .str .x .x18 .x19 16,
      .sub .w .x4 .x5 .x6, .sub .x .x0 .x1 .x30, .rev .x9 .x10,
      .ldrb .x11 .x20 0, .ldrb .x21 .x22 4095, .strb .x23 .x24 7, .strb .x25 .x26 4095])
      (.nonzero .x .x2))

#guard AArch64.printer.function sampleA64 == [
  "cbz x2, 20f",
  "22:",
  "add w4, w5, w6",
  "add x0, x1, x30",
  "add x1, x1, #64",
  "sub x2, x2, #1",
  "and w7, w8, w9",
  "orr w7, w8, w9",
  "eor x7, x8, x9",
  "ror w13, w8, #25",
  "lsr w14, w15, #10",
  "rev w12, w12",
  "movz w13, #12184, lsl #0",
  "movk w13, #17034, lsl #16",
  "ldr w12, [x1, #60]",
  "str w12, [x3, #4]",
  "ldr x16, [x17, #8]",
  "str x18, [x19, #16]",
  "sub w4, w5, w6",
  "sub x0, x1, x30",
  "rev x9, x10",
  "ldrb w11, [x20, #0]",
  "ldrb w21, [x22, #4095]",
  "strb w23, [x24, #7]",
  "strb w25, [x26, #4095]",
  "cbnz x2, 22b",
  "b 21f",
  "20:",
  "21:",
  "ret"
]

/-- Every x86 (32-bit) instruction form, every operand form, and both conditions. -/
def sampleX86 : Prog X86.isa :=
  .seq (.block [.mov .eax (.mem { base := .esp, disp := 16 }), .alu .test .ebp (.reg .ebp)])
    (.ite .e (.block [])
      (.loop (.block [
        .mov .ebx (.reg .eax), .mov .ecx (.imm 0xfffffffe), .mov .edx (.mem { base := .esi }),
        .store { base := .eax, disp := 96 } .ebx,
        .alu .add .ecx (.imm 0x428a2f98), .alu .adc .ecx (.reg .edx), .alu .sub .ebp (.imm 1),
        .alu .sbb .ecx (.reg .edx), .alu .and .ebx (.mem { base := .esi, disp := 28 }),
        .alu .or .ebx (.reg .edx), .alu .xor .ebx (.reg .ecx), .alu .cmp .edi (.imm 64),
        .shift .ror .ebx 6, .shift .shr .eax 10, .bswap .eax]) .ne))

#guard X86.printer.function sampleX86 == [
  "mov eax, DWORD PTR [esp+16]",
  "test ebp, ebp",
  "je 20f",
  "22:",
  "mov ebx, eax",
  "mov ecx, -2",
  "mov edx, DWORD PTR [esi]",
  "mov DWORD PTR [eax+96], ebx",
  "add ecx, 1116352408",
  "adc ecx, edx",
  "sub ebp, 1",
  "sbb ecx, edx",
  "and ebx, DWORD PTR [esi+28]",
  "or ebx, edx",
  "xor ebx, ecx",
  "cmp edi, 64",
  "ror ebx, 6",
  "shr eax, 10",
  "bswap eax",
  "jne 22b",
  "jmp 21f",
  "20:",
  "21:",
  "ret"
]

/-- The x86 (32-bit) byte instructions, every 8-bit register name, and `jb`/`jae`. -/
def sampleX86Bytes : Prog X86.isa :=
  .seq (.block ([.movzx8 .eax { base := .esi, disp := 32 }, .movzx8 .edi { base := .ebp }] ++
      [X86.Reg8.al, .cl, .dl, .bl].map (.store8 { base := .ebx, disp := 5 })))
    (.seq (.ite .b (.block []) (.block [])) (.ite .ae (.block []) (.block [])))

#guard X86.printer.function sampleX86Bytes == [
  "movzx eax, BYTE PTR [esi+32]",
  "movzx edi, BYTE PTR [ebp]",
  "mov BYTE PTR [ebx+5], al",
  "mov BYTE PTR [ebx+5], cl",
  "mov BYTE PTR [ebx+5], dl",
  "mov BYTE PTR [ebx+5], bl",
  "jb 20f",
  "jmp 21f",
  "20:",
  "21:",
  "jae 22f",
  "jmp 23f",
  "22:",
  "23:",
  "ret"
]

/-- Every ARMv7 instruction form, every second-operand form, and both conditions. -/
def sampleArm : Prog Arm.isa :=
  .seq (.block [.cmp .r2 (.imm 0)])
    (.ite .eq (.block [])
      (.loop (.block [
        .mov .r12 (.imm 255), .mov .lr (.reg .r4), .mov .r12 (.shifted .r8 .ror 6),
        .mov .r12 (.shifted .r8 .lsr 10), .mov .r12 (.shifted .r8 .lsl 3),
        .dp .add .r1 .r1 (.imm 64), .dp .sub .r4 .r5 (.reg .r6),
        .dp .and .r7 .r8 (.reg .lr), .dp .orr .r9 .r10 (.reg .r11),
        .dp .eor .r12 .r12 (.shifted .r8 .ror 11),
        .movw .r12 0x2f98, .movt .r12 0x428a, .rev .r12 .r12,
        .ldr .r12 .r1 60, .str .lr .r3 100, .ldrb .r5 .r6 4095, .strb .lr .r7 3, .ldrSp .r4 8,
        .subs .r2 .r2 (.imm 1)]) .ne))

#guard Arm.printer.function sampleArm == [
  "cmp r2, #0",
  "beq 20f",
  "22:",
  "mov r12, #255",
  "mov lr, r4",
  "ror r12, r8, #6",
  "lsr r12, r8, #10",
  "lsl r12, r8, #3",
  "add r1, r1, #64",
  "sub r4, r5, r6",
  "and r7, r8, lr",
  "orr r9, r10, r11",
  "eor r12, r12, r8, ror #11",
  "movw r12, #12184",
  "movt r12, #17034",
  "rev r12, r12",
  "ldr r12, [r1, #60]",
  "str lr, [r3, #100]",
  "ldrb r5, [r6, #4095]",
  "strb lr, [r7, #3]",
  "ldr r4, [sp, #8]",
  "subs r2, r2, #1",
  "bne 22b",
  "b 21f",
  "20:",
  "21:",
  "bx lr"
]

#guard Arm.encodable 0xff000000 && Arm.encodable 0x3fc && !Arm.encodable 0x101 && !Arm.encodable 0x1fe00

#guard Rust.escape "ld1 {v0.4s}, [x1] \\ \"q\"" == "ld1 {{v0.4s}}, [x1] \\\\ \\\"q\\\""

end VG.Test

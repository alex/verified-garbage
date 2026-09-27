import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print

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

#guard Rust.escape "ld1 {v0.4s}, [x1] \\ \"q\"" == "ld1 {{v0.4s}}, [x1] \\\\ \\\"q\\\""

end VG.Test

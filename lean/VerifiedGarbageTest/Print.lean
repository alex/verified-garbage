import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.TCB.PPC64LE.Print

/-!
# Golden tests for the trusted printers

The printers are part of the TCB but not verified; these tests pin down their
output for every construct, so that changes to them are deliberate and show
up in review.
-/

namespace VG.Test

/-- The lines of a printed function, a call shown as `<call name>`. -/
def text (ls : List Line) : List String :=
  ls.map fun | .text s => s | .call n => s!"<call {n}>"

open X86_64

/-- Every `Code` constructor, nested. -/
def sample : Prog isa :=
  .seq (.block [.alu .xor .rax (.reg .rax)])
    (.ite .ne
      (.loop (.block [.alu .add .rax (.mem { base := .rdi, index := some .rcx, scale := 8, disp := -8 }),
                      .alu .sub .rcx (.imm 1)]) .ne)
      (.block [.store { base := .rsi, disp := 16 } .rax, .mov .rdx (.imm (-1))]))

#guard text (printer.function sample) == [
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

/-! `Rust.badCall`: the first call that is not of the code it runs. -/

/-- The printed code of the functions `f`, `g` and `k`, which calls `g`. -/
def printedFG : String → Option (List Line)
  | "f" => some (printer.function (.block [.mov .rax (.imm 1)]))
  | "g" => some (printer.function (.block [.mov .rax (.imm 2)]))
  | "k" => some (printer.function (.call "g" (.block [.mov .rax (.imm 2)])))
  | _ => none

-- The same code written twice is two values in memory: the later call of
-- `f` is compared by its printed code.
#guard Rust.badCall printer printedFG
  [("f", .block [.mov .rax (.imm 1)]), ("g", .block [.mov .rax (.imm 2)]),
   ("f", .block [.mov .rax (.imm 1)])] == none
#guard Rust.badCall printer printedFG [("h", .block [])] == some ("h", false)
#guard Rust.badCall printer printedFG
  [("f", .block [.mov .rax (.imm 1)]), ("g", .block [.mov .rax (.imm 1)])] == some ("g", true)
-- A later call of a function whose first call is of its code.
#guard Rust.badCall printer printedFG
  [("f", .block [.mov .rax (.imm 1)]), ("f", .block [.mov .rax (.imm 2)])] == some ("f", true)
-- Calls nested in a call's code are in `Code.calls`: `k` prints as it should,
-- but the code its call of `g` runs does not.
#guard Rust.badCall printer printedFG
  (Code.calls (.seq (.call "k" (.call "g" (.block [.mov .rax (.imm 2)])))
    (.call "f" (.block [.mov .rax (.imm 1)])) : Prog isa)) == none
#guard Rust.badCall printer printedFG
  (Code.calls (.call "k" (.call "g" (.block [.mov .rax (.imm 3)])) : Prog isa)) ==
  some ("g", true)

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

#guard text (printer.function sample32) == [
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

#guard text (printer.function sample8) == [
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

-- A displacement is encoded in 32 bits, sign-extended: the printer refuses
-- one outside `[-2^31, 2^31)`, for every kind of memory operand, and accepts
-- the bounds.
#guard printer.unencodable (.mov .rax (.mem { base := .rdi, disp := 2147483647 })) == none
#guard printer.unencodable (.store { base := .rdi, index := some .rcx, disp := -2147483648 } .rax) ==
  none
#guard printer.unencodable (.mov .rax (.mem { base := .rdi, disp := 2147483648 })) ==
  some "the displacement of the memory operand [rdi+2147483648] does not fit in 32 bits"
#guard printer.unencodable (.store { base := .rdi, index := some .rcx, disp := -2147483649 } .rax) ==
  some "the displacement of the memory operand [rdi+rcx*1-2147483649] does not fit in 32 bits"
#guard (printer.unencodable (.vmovdqu32Store { base := .rsi, disp := 4294967304 } .xmm0)).isSome
#guard (printer.unencodable (.adox .rax (.mem { base := .rsi, disp := -4294967304 }))).isSome
#guard printer.unencodable (.alu .add .rax (.imm 0x7fffffff)) == none

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

#guard text (printer.function sample64) == [
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
      .ldr .w .x12 .x1 60, .str .w .x12 .x3 4, .ldr .x .x16 .x17 8, .str .x .x20 .x19 16,
      .sub .w .x4 .x5 .x6, .sub .x .x0 .x1 .x30, .rev .x9 .x10,
      .ldrb .x11 .x20 0, .ldrb .x21 .x22 4095, .strb .x23 .x24 7, .strb .x25 .x26 4095,
      .ldrSp .x9 0, .ldrSp .x10 32760])
      (.nonzero .x .x2))

#guard text (AArch64.printer.function sampleA64) == [
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
  "str x20, [x19, #16]",
  "sub w4, w5, w6",
  "sub x0, x1, x30",
  "rev x9, x10",
  "ldrb w11, [x20, #0]",
  "ldrb w21, [x22, #4095]",
  "strb w23, [x24, #7]",
  "strb w25, [x26, #4095]",
  "ldr x9, [sp, #0]",
  "ldr x10, [sp, #32760]",
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

#guard text (X86.printer.function sampleX86) == [
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

#guard text (X86.printer.function sampleX86Bytes) == [
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

#guard text (Arm.printer.function sampleArm) == [
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

/-- Every PPC64LE instruction form, and every condition. -/
def samplePPC : Prog PPC64LE.isa :=
  .seq (.ite (.zero .d .r5) (.block []) (.block []))
  (.ite (.zero .w .r6) (.block [])
    (.loop (.block [
      .add .r3 .r4 .r5, .sub .r6 .r7 .r8, .addi .r4 .r4 64, .subi .r5 .r5 1, .subi .r5 .r5 32768,
      .li .r9 32767, .lis .r10 0x428a, .lis .r10 0xb5c0, .ori .r10 .r10 0x2f98,
      .oris .r11 .r11 0xffff,
      .logic .and .r0 .r2 .r31, .logic .or .r14 .r15 .r16, .logic .xor .r17 .r18 .r19,
      .rotr .w .r12 .r8 25, .rotr .w .r12 .r8 0, .rotr .d .r12 .r8 28, .rotr .d .r12 .r8 0,
      .lsr .w .r20 .r21 10, .lsr .w .r20 .r21 0, .lsr .d .r22 .r23 7, .lsl .r24 .r25 32,
      .load .w .r12 .r4 60, .load .d .r26 .r27 32764, .store .w .r12 .r3 4, .store .d .r28 .r29 8,
      .lbz .r30 .r4 0, .stb .r30 .r3 32767,
      .loadRev .w .r7 .r4 .r8, .loadRev .d .r7 .r4 .r8, .storeRev .w .r7 .r3 .r8,
      .storeRev .d .r7 .r3 .r0,
      .mflr .r0, .mtlr .r0]) (.nonzero .w .r5)))

#guard text (PPC64LE.printer.function samplePPC) == [
  "cmpldi %cr0, %r5, 0",
  "beq %cr0, 20f",
  "b 21f",
  "20:",
  "21:",
  "cmplwi %cr0, %r6, 0",
  "beq %cr0, 22f",
  "24:",
  "add %r3, %r4, %r5",
  "subf %r6, %r8, %r7",
  "addi %r4, %r4, 64",
  "addi %r5, %r5, -1",
  "addi %r5, %r5, -32768",
  "li %r9, 32767",
  "lis %r10, 17034",
  "lis %r10, -19008",
  "ori %r10, %r10, 12184",
  "oris %r11, %r11, 65535",
  "and %r0, %r2, %r31",
  "or %r14, %r15, %r16",
  "xor %r17, %r18, %r19",
  "rlwinm %r12, %r8, 7, 0, 31",
  "rlwinm %r12, %r8, 0, 0, 31",
  "rldicl %r12, %r8, 36, 0",
  "rldicl %r12, %r8, 0, 0",
  "rlwinm %r20, %r21, 22, 10, 31",
  "rlwinm %r20, %r21, 0, 0, 31",
  "rldicl %r22, %r23, 57, 7",
  "rldicr %r24, %r25, 32, 31",
  "lwz %r12, 60(%r4)",
  "ld %r26, 32764(%r27)",
  "stw %r12, 4(%r3)",
  "std %r28, 8(%r29)",
  "lbz %r30, 0(%r4)",
  "stb %r30, 32767(%r3)",
  "lwbrx %r7, %r4, %r8",
  "ldbrx %r7, %r4, %r8",
  "stwbrx %r7, %r3, %r8",
  "stdbrx %r7, %r3, %r0",
  "mflr %r0",
  "mtlr %r0",
  "cmplwi %cr0, %r5, 0",
  "bne %cr0, 24b",
  "b 23f",
  "22:",
  "23:",
  "blr"
]

-- Every register name.
#guard ([PPC64LE.Reg.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15,
    .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].map PPC64LE.Reg.name) ==
  ["%r0", "%r2", "%r3", "%r4", "%r5", "%r6", "%r7", "%r8", "%r9", "%r10", "%r11", "%r12",
   "%r14", "%r15", "%r16", "%r17", "%r18", "%r19", "%r20", "%r21", "%r22", "%r23", "%r24",
   "%r25", "%r26", "%r27", "%r28", "%r29", "%r30", "%r31"]

#guard Arm.encodable 0xff000000 && Arm.encodable 0x3fc && !Arm.encodable 0x101 && !Arm.encodable 0x1fe00

#guard Rust.escape "ld1 {v0.4s}, [x1] \\ \"q\"" == "ld1 {{v0.4s}}, [x1] \\\\ \\\"q\\\""

/-! ## Calls

A call is its own line, whatever the callee's code; the emitter renders it as
the call instruction with the callee's symbol as a `sym` operand. -/

/-- A call between two blocks, on every target. -/
def callSample : Prog X86_64.isa :=
  .seq (.block [.mov .rdi (.reg .rbx)]) (.seq (.call "vg_f" (.block [.alu .add .rax (.imm 1)]))
    (.block [.mov .rax (.reg .rdx)]))

#guard printer.function callSample == [
  .text "mov rdi, rbx", .call "vg_f", .text "mov rax, rdx", .text "ret"]
#guard AArch64.printer.function (.call "vg_f" (.block []) : Prog AArch64.isa) == [.call "vg_f", .text "ret"]
#guard X86.printer.function (.call "vg_f" (.block []) : Prog X86.isa) == [.call "vg_f", .text "ret"]
#guard Arm.printer.function (.call "vg_f" (.block []) : Prog Arm.isa) == [.call "vg_f", .text "bx lr"]
#guard PPC64LE.printer.function (.call "vg_f" (.block []) : Prog PPC64LE.isa) ==
  [.call "vg_f", .text "blr"]
#guard Rust.line PPC64LE.printer.call (.call "vg_f") == "        \"bl {vg_f}\",\n"

#guard Rust.line printer.call (.call "vg_f") == "        \"call {vg_f}\",\n"
#guard Rust.line Arm.printer.call (.call "vg_f") == "        \"bl {vg_f}\",\n"
#guard Rust.line printer.call (.text "mov rax, QWORD PTR [rdi]") ==
  "        \"mov rax, QWORD PTR [rdi]\",\n"

/-! ## Frames

A frame is its push, its body and its pop, each printed as the target's
instructions. -/

-- Save the link register around a call (AArch64).
#guard text (AArch64.printer.function
    (.frame (.push .x30) (.call "vg_f" (.block [])) (.pop .x30) : Prog AArch64.isa)) == [
  "str x30, [sp, #-16]!", "<call vg_f>", "ldr x30, [sp], #16", "ret"]

-- Pass two arguments on the stack, inside a frame saving `lr` (ARMv7). A pop
-- loads the lowest word of its frame.
#guard text (Arm.printer.function
    (.frame (.push [.lr])
      (.frame (.push [.r0, .r1]) (.call "vg_f" (.block [])) (.pop .r2 8)) (.pop .lr 4) :
      Prog Arm.isa)) == [
  "push {lr}", "push {r0, r1}", "<call vg_f>", "ldr r2, [sp], #8", "ldr lr, [sp], #4", "bx lr"]

-- Pass two arguments on the stack (x86): the first pushed is the higher
-- address.
#guard text (X86.printer.function
    (.frame (.push [.ecx, .eax]) (.call "vg_f" (.block [])) (.pop .edx 2) : Prog X86.isa)) == [
  "push ecx", "push eax", "<call vg_f>", "pop edx", "pop edx", "ret"]

-- Pass two arguments on the stack, inside a frame saving `rbx` (x86-64).
#guard text (printer.function
    (.frame (.push [.rbx])
      (.frame (.push [.rcx, .rax]) (.call "vg_f" (.block [])) (.pop .rdx 2)) (.pop .rbx 1) :
      Prog X86_64.isa)) == [
  "push rbx", "push rcx", "push rax", "<call vg_f>", "pop rdx", "pop rdx", "pop rbx", "ret"]

-- Save the link register around a call (PPC64LE): through `r0`, in a frame
-- with a back chain.
#guard text (PPC64LE.printer.function
    (.seq (.block [.mflr .r0])
      (.seq (.frame (.push .r0) (.call "vg_f" (.block [])) (.pop .r0)) (.block [.mtlr .r0])) :
      Prog PPC64LE.isa)) == [
  "mflr %r0", "stdu %r1, -48(%r1)", "std %r0, 32(%r1)", "<call vg_f>", "ld %r0, 32(%r1)",
  "addi %r1, %r1, 48", "mtlr %r0", "blr"]

#guard Rust.line Arm.printer.call (.text "push {r4, lr}") == "        \"push {{r4, lr}}\",\n"

/-! ## CPU features

`Code.requires` collects what every instruction needs, through calls and
frames; `Rust.featureCheck` accepts exactly the declared set; the emitted
`# Safety` item and constant list it. -/

/-- A stand-in for an ISA's `requires`, over instructions named by strings. -/
def req : String → List String
  | "sha256rnds2" => ["sha"]
  | "pshufb" => ["ssse3"]
  | "pblendw" => ["sse4.1"]
  | _ => []

def featureSample : Code String Unit :=
  .seq (.block ["mov", "sha256rnds2", "sha256rnds2"])
    (.ite () (.loop (.call "vg_f" (.block ["pshufb"])) ())
      (.frame "push" (.block ["pblendw"]) "pop"))

#guard featureSample.requires req == ["sha", "sha", "ssse3", "sse4.1"]
#guard (Code.block ["mov", "add"] : Code String Unit).requires req == []

/-- The error of a failed check. -/
def err : Except String Unit → Option String
  | .error e => some e
  | .ok _ => none

def safeDoc : String := "Does things.\n\n# Safety\n\n* `p` must be valid."

#guard (Rust.featureCheck "f" "No safety requirements." [] []).toBool
#guard (Rust.featureCheck "f" safeDoc (featureSample.requires req) ["sse4.1", "sha", "ssse3"]).toBool
-- An undeclared feature, an unneeded one, and a doc the item can't be added to.
#guard err (Rust.featureCheck "f" safeDoc ["sha", "ssse3"] ["sha"]) ==
  some "f requires the CPU feature ssse3 but does not declare it"
#guard err (Rust.featureCheck "f" safeDoc ["sha"] ["sha", "avx2"]) ==
  some "f declares the CPU feature avx2, which none of its code requires"
#guard err (Rust.featureCheck "f" "No safety requirements." ["sha"] ["sha"]) ==
  some "f needs CPU features but its doc has no `# Safety` section"
#guard err (Rust.featureCheck "f" (safeDoc ++ "\n\n# Panics\n\nNever.") ["sha"] ["sha"]) ==
  some "f needs CPU features but its doc does not end with its `# Safety` section"

#guard Rust.featureDoc safeDoc [] == safeDoc
#guard Rust.featureDoc safeDoc ["sha"] ==
  safeDoc ++ "\n* The CPU must support the `sha` target feature."
#guard Rust.featureDoc safeDoc ["sha", "ssse3"] ==
  safeDoc ++ "\n* The CPU must support the `sha` and `ssse3` target features."
#guard Rust.featureDoc safeDoc ["sha", "ssse3", "sse4.1"] ==
  safeDoc ++ "\n* The CPU must support the `sha`, `ssse3` and `sse4.1` target features."

#guard Rust.featuresConst "vg_f" [] == ""
#guard Rust.featuresConst "vg_sha256_compress_shani" ["sha", "ssse3"] ==
  "/// The CPU features `vg_sha256_compress_shani` requires (`Artifact.features`).\n\
  pub(crate) const VG_SHA256_COMPRESS_SHANI_FEATURES: &[&str] = &[\"sha\", \"ssse3\"];\n\n"

end VG.Test

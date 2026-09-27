import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.Rust

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

#guard printer.function "f" sample == [
  "xor rax, rax",
  "jne .Lf_0",
  "mov QWORD PTR [rsi+16], rax",
  "mov rdx, -1",
  "jmp .Lf_1",
  ".Lf_0:",
  ".Lf_2:",
  "add rax, QWORD PTR [rdi+rcx*8-8]",
  "sub rcx, 1",
  "jne .Lf_2",
  ".Lf_1:",
  "ret"
]

#guard Rust.escape "ld1 {v0.4s}, [x1] \\ \"q\"" == "ld1 {{v0.4s}}, [x1] \\\\ \\\"q\\\""

end VG.Test

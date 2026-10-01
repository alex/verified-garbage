import VerifiedGarbage.TCB.X86_64.Isa

/-! Constant-time byte comparison. Only the public lengths control branches. -/
namespace VG.Impl.Ct.X86_64
open VG.X86_64

def step : List Instr := [
  .movzx8 .r9 { base := .rdi, index := some .r8 },
  .movzx8 .r10 { base := .rdx, index := some .r8 },
  .alu .xor .r9 (.reg .r10), .alu .or .rax (.reg .r9),
  .alu .add .r8 (.imm 1), .alu .cmp .r8 (.reg .rsi)]

def finish : Prog isa := .block [.alu .sub .rax (.imm 1), .shift .shr .rax 63]

def equal : Prog isa :=
  .seq (.block [.mov .r8 (.imm 0), .alu .cmp .r8 (.reg .rsi)])
    (.seq (.ite .e (.block []) (.loop (.block step) .ne)) finish)

def eq : Prog isa :=
  .seq (.block [.mov .rax (.imm 0), .mov .r8 (.reg .rsi), .alu .cmp .r8 (.reg .rcx)])
    (.ite .e equal (.block []))
end VG.Impl.Ct.X86_64

import VerifiedGarbage.TCB.X86.Isa

/-! Byte comparison with a four-byte frame holding the caller's EBX. -/
namespace VG.Impl.Ct.X86
open VG.X86

def step : List Instr := [
  .mov .eax (.mem {base := .esp, disp := 8}), .alu .add .eax (.reg .ecx),
  .movzx8 .edx {base := .eax},
  .mov .eax (.mem {base := .esp, disp := 16}), .alu .add .eax (.reg .ecx),
  .movzx8 .eax {base := .eax},
  .alu .xor .edx (.reg .eax), .alu .or .ebx (.reg .edx),
  .alu .add .ecx (.imm 1), .mov .eax (.mem {base := .esp, disp := 12}), .alu .cmp .ecx (.reg .eax)]

def finish : Prog isa := .block [.mov .eax (.reg .ebx), .alu .sub .eax (.imm 1), .shift .shr .eax 31]

def equal : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .eax (.mem {base := .esp, disp := 12}), .alu .cmp .ecx (.reg .eax)])
    (.seq (.ite .e (.block []) (.loop (.block step) .ne)) finish)

def body : Prog isa :=
  .seq (.block [.mov .eax (.mem {base := .esp, disp := 12}),
    .mov .edx (.mem {base := .esp, disp := 20}), .alu .cmp .eax (.reg .edx)])
    (.ite .e equal (.block [.mov .eax (.imm 0)]))

def eq : Prog isa := .frame (.push [.ebx]) body (.pop .ebx 1)
end VG.Impl.Ct.X86

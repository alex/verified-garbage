import VerifiedGarbage.TCB.X86_64.Isa

/-! Word stores followed by a byte tail. Unaligned stores are permitted on x86-64. -/
namespace VG.Impl.Zeroize.X86_64
open VG.X86_64

def step (word : Bool) : List Instr :=
  [if word then .store { base := .rdi } .rax else .store8 { base := .rdi } .rax,
   .alu .add .rdi (.imm (if word then 8 else 1)), .alu .sub .rdx (.imm 1)]

def loop (word : Bool) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 0)])
    (.ite .e (.block []) (.loop (.block (step word)) .ne))

def zeroize : Prog isa :=
  .seq (.block [.mov .rax (.imm 0), .mov .rdx (.reg .rsi), .shift .shr .rdx 3,
    .alu .and .rsi (.imm 7)])
    (.seq (loop true) (.seq (.block [.mov .rdx (.reg .rsi)]) (loop false)))
end VG.Impl.Zeroize.X86_64

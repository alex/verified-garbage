import VerifiedGarbage.TCB.X86.Isa

/-! Four-byte stores followed by a byte tail, using only caller-saved registers. -/
namespace VG.Impl.Zeroize.X86
open VG.X86

def step (word : Bool) : List Instr :=
  [if word then .store { base := .ecx } .eax else .store8 { base := .ecx } .al,
   .alu .add .ecx (.imm (if word then 4 else 1)), .alu .sub .edx (.imm 1)]

def loop (word : Bool) : Prog isa :=
  .seq (.block [.alu .cmp .edx (.imm 0)])
    (.ite .e (.block []) (.loop (.block (step word)) .ne))

def zeroize : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .mov .ecx (.mem {base := .esp, disp := 4}),
    .mov .edx (.mem {base := .esp, disp := 8}), .shift .shr .edx 2])
    (.seq (loop true) (.seq (.block [.mov .edx (.mem {base := .esp, disp := 8}),
      .alu .and .edx (.imm 3)]) (loop false)))
end VG.Impl.Zeroize.X86

import VerifiedGarbage.TCB.X86.Isa

/-! Eight four-byte stores (32 bytes) at a time, then four-byte stores, then
a byte tail, using only caller-saved registers. -/
namespace VG.Impl.Zeroize.X86
open VG.X86

def step (word : Bool) : List Instr :=
  [if word then .store { base := .ecx } .eax else .store8 { base := .ecx } .al,
   .alu .add .ecx (.imm (if word then 4 else 1)), .alu .sub .edx (.imm 1)]

/-- Eight words, at `ecx`, `ecx + 4`, …, `ecx + 28`. -/
def wideStep : List Instr :=
  [.store { base := .ecx } .eax, .store { base := .ecx, disp := 4 } .eax,
   .store { base := .ecx, disp := 8 } .eax, .store { base := .ecx, disp := 12 } .eax,
   .store { base := .ecx, disp := 16 } .eax, .store { base := .ecx, disp := 20 } .eax,
   .store { base := .ecx, disp := 24 } .eax, .store { base := .ecx, disp := 28 } .eax,
   .alu .add .ecx (.imm 32), .alu .sub .edx (.imm 1)]

/-- `body` `edx` times. -/
def loopOf (body : List Instr) : Prog isa :=
  .seq (.block [.alu .cmp .edx (.imm 0)])
    (.ite .e (.block []) (.loop (.block body) .ne))

def loop (word : Bool) : Prog isa := loopOf (step word)

def zeroize : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .mov .ecx (.mem {base := .esp, disp := 4}),
    .mov .edx (.mem {base := .esp, disp := 8}), .shift .shr .edx 5])
    (.seq (loopOf wideStep)
    (.seq (.block [.mov .edx (.mem {base := .esp, disp := 8}), .shift .shr .edx 2, .alu .and .edx (.imm 7)])
    (.seq (loop true) (.seq (.block [.mov .edx (.mem {base := .esp, disp := 8}),
      .alu .and .edx (.imm 3)]) (loop false)))))
end VG.Impl.Zeroize.X86

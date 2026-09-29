import VerifiedGarbage.Impl.MlKem.X86_64.Common

/-!
# ML-KEM on x86-64: `vg_mlkem_add` and `vg_mlkem_sub`

`add(f = rdi, g = rsi)` and `sub(f = rdi, g = rsi)` run over the 256
coefficients with `rdi` and `rsi` pointing at coefficient `i` of `f` and
`g`, and `rcx = 256 - i` counting down: `f[i] + g[i]` (for `sub`,
`f[i] + q - g[i]`), less than `2q`, is reduced with `csubQ` and stored to
`f[i]`. Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- Advance the two pointers and count down. -/
def step2 : List Instr :=
  [.alu .add .rdi (.imm 4), .alu .add .rsi (.imm 4), .alu .sub .rcx (.imm 1)]

def addBody : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 0)), .alu32 .add .rax (.mem (at_ .rsi 0))] ++ csubQ .rax .rdx ++
    [.store32 (at_ .rdi 0) .rax] ++ step2

def subBody : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 0)), .alu32 .add .rax (.imm qImm), .alu32 .sub .rax (.mem (at_ .rsi 0))] ++
    csubQ .rax .rdx ++ [.store32 (at_ .rdi 0) .rax] ++ step2

def add : Prog isa := .seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block addBody) .ne)

def sub : Prog isa := .seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block subBody) .ne)

end VG.Impl.MlKem.X86_64

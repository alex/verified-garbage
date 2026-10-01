import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec

/-!
# ML-DSA on x86-64: `vg_mldsa_add` and `vg_mldsa_sub`

`add(f = rdi, g = rsi)` and `sub(f = rdi, g = rsi)` compute on four
coefficients at a time, as doublewords of SSE registers (see `Vec.lean`),
with `rdi` and `rsi` pointing at coefficient `4i` of `f` and `g`, and
`rcx = 64 - i` counting down: `f + g`, less than `2q`, is reduced with
`vcsub` (for `sub`, `f - g`, in `(-q, q)`, with `vcadd`) and stored to `f`,
with `q` in the doublewords of `xmm15`. Every address and branch depends
only on the pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb rcxLoop)

/-- `q` in the doublewords of `xmm15`, through `rax`. -/
def qPro : List Instr := [.mov32 .rax (.imm 8380417), .xop (.movq .xmm15 .rax), .xop (.pshufd .xmm15 .xmm15 0)]

/-- Store `xmm0` to `f` and advance the two pointers. -/
def accTail : List Instr :=
  [.movdquStore (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 16), .alu .add .rsi (.imm 16)]

def addBody : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0), xb .paddd .xmm0 .xmm1] ++
    vcsub .xmm0 .xmm2 ++ accTail

def subBody : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0), xb .psubd .xmm0 .xmm1] ++
    vcadd .xmm0 .xmm2 ++ accTail

def add : Prog isa := .seq (.block qPro) (rcxLoop 64 addBody)

def sub : Prog isa := .seq (.block qPro) (rcxLoop 64 subBody)

end VG.Impl.MlDsa.X86_64.Arith

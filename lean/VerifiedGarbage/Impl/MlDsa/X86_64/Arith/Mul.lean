import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Common

/-!
# ML-DSA on x86-64: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`multiplyNTT(h = rdi, f = rsi, g = rdx)` and `multiplyAddNTT(h = rdi,
f = rsi, g = rdx)` run over the 256 coefficients with `rdi`, `rsi` and `r8`
(`g`, as `mul` writes `rdx`) pointing at coefficient `i` of `h`, `f` and
`g`, and `rcx = 256 - i` counting down: the product `f[i] · g[i]` (by
`mul`, less than `q²`; for `multiplyAddNTT`, plus `h[i]`) is reduced with
`reduce` and stored to `h[i]`. Every address and branch depends only on the
pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64

/-- Advance the three pointers and count down. -/
def step3 : List Instr :=
  [.alu .add .rdi (.imm 4), .alu .add .rsi (.imm 4), .alu .add .r8 (.imm 4), .alu .sub .rcx (.imm 1)]

/-- `f[i] · g[i]`, in `rax`. -/
def mulHead : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .r9 (.mem (at_ .r8 0)), .mul .r9]

/-- `f[i] · g[i] + h[i]`, in `rax`. -/
def mulAddHead : List Instr :=
  mulHead ++ [.mov32 .r9 (.mem (at_ .rdi 0)), .alu .add .rax (.reg .r9)]

def mulBody : List Instr := mulHead ++ reduce ++ [.store32 (at_ .rdi 0) .r10] ++ step3

def mulAddBody : List Instr := mulAddHead ++ reduce ++ [.store32 (at_ .rdi 0) .r10] ++ step3

def mul : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rdx)]) (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block mulBody) .ne))

def mulAdd : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rdx)]) (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block mulAddBody) .ne))

end VG.Impl.MlDsa.X86_64.Arith

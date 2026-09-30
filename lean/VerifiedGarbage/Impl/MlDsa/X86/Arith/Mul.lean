import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`multiplyNTT(h, f, g)` and `multiplyAddNTT(h, f, g)` run over the 256
coefficients with `ebp`, `esi` and `edi` pointing at coefficient `i` of `h`,
`f` and `g`, and `ecx` the coefficients left. The product `f[i] · g[i]`
(by `mul`, less than `q²`) is reduced twice by Montgomery: `mredRaw` leaves
`t < 2q` congruent to `f[i] · g[i] · 2⁻³²`, and `mred` of `t · (2⁶⁴ mod q)`
(less than `2q²`) leaves `f[i] · g[i] mod q`, in `ebx`. For
`multiplyAddNTT`, `h[i]` is added and the sum reduced. Every address and
branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86.Arith

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `2⁶⁴ mod q`. -/
def r2Imm : BitVec 32 := 2365951

/-- `ebx ← f[i] · g[i] mod q`. -/
def mulHead : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.mem (at_ .edi 0)), .mul .edx] +++ mredRaw .ebx +++
  [.mov .eax (.reg .ebx), .mov .edx (.imm r2Imm), .mul .edx] +++ mred .ebx

/-- Store `ebx` to `h[i]`, and on to the next coefficient. -/
def mulTail : List Instr :=
  [.store (at_ .ebp 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4),
    .alu .sub .ecx (.imm 1)]

def mulBody : List Instr := mulHead +++ mulTail

def mulAddBody : List Instr :=
  mulHead +++ .alu .add .ebx (.mem (at_ .ebp 0)) :: csubQ .ebx .edx +++ mulTail

/-- `ebp = h`, `esi = f`, `edi = g`, `ecx = 256`. -/
def mulInit : List Instr :=
  [.mov .ebp (.mem (at_ .esp 20)), .mov .esi (.mem (at_ .esp 24)), .mov .edi (.mem (at_ .esp 28)),
    .mov .ecx (.imm 256)]

def mul : Prog isa := leaf (.seq (.block mulInit) (.loop (.block mulBody) .ne))

def mulAdd : Prog isa := leaf (.seq (.block mulInit) (.loop (.block mulAddBody) .ne))

end VG.Impl.MlDsa.X86.Arith

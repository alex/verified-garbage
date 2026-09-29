import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_check_ek`

A leaf (`leaf`) looping over the 384 groups of three bytes of the first 1152
bytes of `ek`, with `esi` at the group and `ecx` the groups left. The two
12-bit fields of a group are computed in `eax` and `ebp` (as in `decode12`);
`sub r, q` borrows exactly when `r < q`, and `sbb r, r` turns the borrow into
the mask `0xffffffff` (or 0), which is ANDed into `ebx` (from `0xffffffff`).
The result is its low bit. Every address and branch depends only on the
pointer.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

def ekBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .edx (at_ .esi 1), .mov .ebp (.reg .edx), .alu .and .edx (.imm 15),
    .shift .ror .edx 24, .alu .add .eax (.reg .edx), .shift .shr .ebp 4, .movzx8 .edx (at_ .esi 2),
    .shift .ror .edx 28, .alu .add .ebp (.reg .edx),
    .alu .sub .eax (.imm Q), .alu .sbb .eax (.reg .eax), .alu .and .ebx (.reg .eax),
    .alu .sub .ebp (.imm Q), .alu .sbb .ebp (.reg .ebp), .alu .and .ebx (.reg .ebp),
    .alu .add .esi (.imm 3), .alu .sub .ecx (.imm 1)]

/-- `esi = ek`, `ecx = 384`, `ebx = 0xffffffff`. -/
def ekInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .ecx (.imm 384), .mov .ebx (.imm 0xffffffff)]

/-- The low bit of `ebx`. -/
def ekEnd : List Instr := [.mov .eax (.reg .ebx), .alu .and .eax (.imm 1)]

def checkEk : Prog isa := leaf (.seq (.block ekInit) (.seq (.loop (.block ekBody) .ne) (.block ekEnd)))

end VG.Impl.MlKem.X86

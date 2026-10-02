import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): the encapsulation key check

`checkEkN n`: a leaf (`leaf`) looping over the `n` groups of three bytes of
the first `3n` bytes of `ek`, with `esi` at the group and `ecx` the groups
left. The two 12-bit fields of a group are computed in `eax` and `ebp` (as in
`decode12`); `sub r, q` borrows exactly when `r < q`, and `sbb r, r` turns the
borrow into the mask `0xffffffff` (or 0), which is ANDed into `ebx` (from
`0xffffffff`). The result is its low bit. Every address and branch depends
only on the pointer. `vg_mlkem768_check_ek` is `checkEk`, over the 384 groups
of `ek[0 : 1152]`.
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

/-- `esi = ek`, `ecx = n`, `ebx = 0xffffffff`. -/
def ekInitN (n : Nat) : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .ecx (.imm (BitVec.ofNat 32 n)), .mov .ebx (.imm 0xffffffff)]

/-- The low bit of `ebx`. -/
def ekEnd : List Instr := [.mov .eax (.reg .ebx), .alu .and .eax (.imm 1)]

def checkEkN (n : Nat) : Prog isa := leaf (.seq (.block (ekInitN n)) (.seq (.loop (.block ekBody) .ne) (.block ekEnd)))

/-- `vg_mlkem768_check_ek`. -/
def checkEk : Prog isa := checkEkN 384

end VG.Impl.MlKem.X86

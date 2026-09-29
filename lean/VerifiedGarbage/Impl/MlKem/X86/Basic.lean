import VerifiedGarbage.TCB.X86.Isa

/-!
# ML-KEM on x86 (32-bit): helpers, `vg_mlkem_add` and `vg_mlkem_sub`

Coefficients are `u32`s less than `q = 3329`. A value `x < 2q` is reduced
with one conditional subtraction without a branch (`csub`): `sub x, q`
borrows exactly when `x < q`, `sbb t, t` turns the borrow into the mask
`t = 0` or `t = 0xffffffff`, and `q & t` is added back.

A function that calls no other one (`leaf`) saves its caller's `ebx`, `esi`,
`edi` and `ebp` in a frame of 16 bytes, `[esp + 12]`, `[esp + 8]`,
`[esp + 4]` and `[esp]`, and reloads them at the end; the frame's pop
reloads `ebx`. Its arguments are then at `[esp + 20]`, `[esp + 24]`, …
(cdecl, above the return address at `[esp + 16]`).

* `add(f, g)`: `f[i] ← (f[i] + g[i]) mod q`;
* `sub(f, g)`: `f[i] ← (f[i] + q - g[i]) mod q`.

Both are the same loop (`mapLoop`) with `esi = f`, `edi = g` and `ecx` the
coefficients left, around the arithmetic `addOp` or `subOp` on `eax = f[i]`,
with `edx` as a temporary. Every address and branch depends only on the
pointers.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `[b + d]` -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `++`, grouping to the right. The kernel evaluates the code (for the
constant-time analysis), and `(a ++ b) ++ c` has it copy `a` twice. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `q` -/
def Q : BitVec 32 := 3329

/-- `r ← r mod q` for `r < 2q`, with the temporary `t`. -/
def csub (r t : Reg) : List Instr :=
  [.alu .sub r (.imm Q), .alu .sbb t (.reg t), .alu .and t (.imm Q), .alu .add r (.reg t)]

/-- The caller's registers a leaf saves, in the order they are pushed. -/
def saveRegs : List Reg := [.ebx, .esi, .edi, .ebp]

/-- Reload `esi`, `edi` and `ebp` from the frame. -/
def restore : List Instr :=
  [.mov .esi (.mem (at_ .esp 8)), .mov .edi (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 0))]

/-- A function that calls no other one, around its `body`. -/
def leaf (body : Prog isa) : Prog isa :=
  .frame (.push saveRegs) (.seq body (.block restore)) (.pop .ebx 4)

/-! ## `add` and `sub` -/

/-- `eax ← (eax + g[i]) mod q`. -/
def addOp : List Instr := .alu .add .eax (.mem (at_ .edi 0)) :: csub .eax .edx

/-- `eax ← (eax + q - g[i]) mod q`. -/
def subOp : List Instr :=
  .alu .add .eax (.imm Q) :: .alu .sub .eax (.mem (at_ .edi 0)) :: csub .eax .edx

/-- One coefficient: `eax = f[i]`, `op`, `f[i] ← eax`, and on to the next. -/
def mapBody (op : List Instr) : List Instr :=
  .mov .eax (.mem (at_ .esi 0)) :: op +++
    [.store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .ecx (.imm 1)]

/-- `esi = f`, `edi = g`, `ecx = 256`. -/
def mapInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 24)), .mov .ecx (.imm 256)]

/-- `op` on each of the 256 coefficients. -/
def mapLoop (op : List Instr) : Prog isa :=
  .seq (.block mapInit) (.loop (.block (mapBody op)) .ne)

def add : Prog isa := leaf (mapLoop addOp)

def sub : Prog isa := leaf (mapLoop subOp)

end VG.Impl.MlKem.X86

import VerifiedGarbage.TCB.X86_64.Isa

/-!
# ML-KEM on x86-64: common code

Pieces of code that the ML-KEM functions share:

* `csubQ r m`: `r ← r mod q` for a 32-bit `r < 2q`, without a branch:
  `sub r, q` sets CF exactly when `r < q`, `sbb m, m` turns it into a mask
  (all ones or zero), and `q` masked with it is added back;
* `reduce`: `r10 ← rax mod q` for `rax < 2³²`, by a Barrett reduction with
  one 64-bit product (`⌊rax · 1290167 / 2³²⌋ · q` subtracted, then
  `csubQ`), with `mul`, which is the only multiplication of the model
  (its timing does not depend on its operands: it is on Intel's DOIT list).
  It uses `rax`, `rdx` and `r11`;
* `storeTab t n`: the table `t 0, …, t (n - 1)` of constants stored as
  `u32`s at `r9` (in the working space: the code has no other memory), with
  immediates. It uses `rax`.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `q = 3329`, as an immediate. -/
def qImm : BitVec 32 := 3329

/-- `r ← r mod q` for `r < 2q` (32 bits), with `m` as a mask. -/
def csubQ (r m : Reg) : List Instr :=
  [.alu32 .sub r (.imm qImm), .alu32 .sbb m (.reg m), .alu32 .and m (.imm qImm),
    .alu32 .add r (.reg m)]

/-- `r10 ← rax mod q` for `rax < 2³²`: `rax · 1290167` (in `rax`), shifted
right by 32, times `q`, subtracted from the copy of `rax` in `r10`, then
`csubQ`. Uses `rdx` and `r11`. -/
def reduce : List Instr :=
  [.mov .r10 (.reg .rax), .mov .r11 (.imm 1290167), .mul .r11, .shift .shr .rax 32,
    .mov .r11 (.imm qImm), .mul .r11, .alu .sub .r10 (.reg .rax)] ++ csubQ .r10 .r11

/-- `t i` to `[r9 + 4i]`. -/
def tabStep (t : Nat → Nat) (i : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 (t i))), .store32 (at_ .r9 (4 * i)) .rax]

/-- The table `t 0, …, t (n - 1)` at `r9`. -/
def storeTab (t : Nat → Nat) (n : Nat) : List Instr := (List.range n).flatMap (tabStep t)

end VG.Impl.MlKem.X86_64

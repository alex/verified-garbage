import VerifiedGarbage.TCB.X86_64.Isa

/-!
# ML-DSA on x86-64: arithmetic modulo `q`

Pieces of code that the ML-DSA arithmetic functions share, for
`q = 8380417 < 2²³`:

* `csubQ r m`: `r ← r mod q` for a 32-bit `r < 2q`, without a branch:
  `sub r, q` sets CF exactly when `r < q`, `sbb m, m` turns it into a mask
  (all ones or zero), and `q` masked with it is added back;
* `reduce`: `r10 ← rax mod q` for any 64-bit `rax` (in particular a product
  of two reduced values, less than `q² < 2⁴⁶`, plus a reduced value), by a
  Barrett reduction: the high half of the 128-bit product of `rax` and
  `⌊2⁶⁴ / q⌋` (in `rdx`, by `mul`) is at most `⌊rax / q⌋` and at least
  `⌊rax / q⌋ - 1`, so `rax` less that quotient times `q` (a second `mul`) is
  less than `2q`, and `csubQ` reduces it. `mul` is the only multiplication of
  the model, and its timing does not depend on its operands (it is on
  Intel's DOIT list). It uses `rax`, `rdx` and `r11`;
* `storeTab t n`: the table `t 0, …, t (n - 1)` of constants stored as
  `u32`s at `r9` (in the working space: the code has no other memory), with
  immediates. It uses `rax`.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- `⌊2⁶⁴ / q⌋`. -/
def barrettImm : BitVec 64 := 2201172575745

/-- `r ← r mod q` for `r < 2q` (32 bits), with `m` as a mask. -/
def csubQ (r m : Reg) : List Instr :=
  [.alu32 .sub r (.imm qImm), .alu32 .sbb m (.reg m), .alu32 .and m (.imm qImm),
    .alu32 .add r (.reg m)]

/-- `r10 ← rax mod q`: the high half of `rax · ⌊2⁶⁴ / q⌋`, times `q`,
subtracted from the copy of `rax` in `r10`, then `csubQ`. Uses `rdx` and
`r11`. -/
def reduce : List Instr :=
  [.mov .r10 (.reg .rax), .movImm64 .r11 barrettImm, .mul .r11, .mov .rax (.reg .rdx),
    .mov .r11 (.imm qImm), .mul .r11, .alu .sub .r10 (.reg .rax)] ++ csubQ .r10 .r11

/-- `t i` to `[r9 + 4i]`. -/
def tabStep (t : Nat → Nat) (i : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 (t i))), .store32 (at_ .r9 (4 * i)) .rax]

/-- The table `t 0, …, t (n - 1)` at `r9`. -/
def storeTab (t : Nat → Nat) (n : Nat) : List Instr := (List.range n).flatMap (tabStep t)

end VG.Impl.MlDsa.X86_64.Arith

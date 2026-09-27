import VerifiedGarbage.TCB.Code

/-!
# AArch64 machine model

**Trusted.** A model of the subset of AArch64 (A64) used by our
implementations. Each instruction's semantics here must agree with the Arm
Architecture Reference Manual for A-profile (DDI 0487), chapter C6 ("A64
Base Instruction Descriptions"); when adding an instruction, cite the section
whose pseudocode it transcribes.

Modelling choices:
* Registers are `x0`–`x30`; the stack pointer is separate and no modelled
  instruction reads or writes it (register number 31, SP or the zero
  register, is never an operand). Every instruction has a 32-bit (`w`) and a
  64-bit (`x`) form; a 32-bit result is zero-extended into the 64-bit
  register (DDI 0487, the pseudocode accessor `X[n, width] = value` sets
  `_R[n] = ZeroExtend(value, 64)`).
* The condition flags are not modelled, and no modelled instruction reads or
  writes them; control flow uses `cbz`/`cbnz`.
* Immediates that the instruction cannot encode make the instruction fault,
  so verified code only ever contains encodable instructions.
* Memory accesses must lie within the state's permitted regions: loads within
  `rd ++ wr`, stores within `wr`; otherwise the instruction faults. Memory is
  little-endian.
* Instructions whose timing depends on their operands (e.g. `udiv`) must never
  be added: the constant-time leakage model assumes they do not exist.
-/

namespace VG.AArch64

inductive Reg
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x30
  deriving DecidableEq, Repr, Inhabited

/-- Operand size: 32-bit (`w` registers) or 64-bit (`x` registers). -/
inductive Size | w | x
  deriving DecidableEq, Repr

abbrev Size.bits : Size → Nat
  | .w => 32
  | .x => 64

structure State where
  gpr : Reg → BitVec 64
  sp : BitVec 64
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region

inductive LogicOp | and | orr | eor
  deriving DecidableEq, Repr

inductive Instr
  /-- `add d, n, m` (ADD (shifted register), no shift) -/
  | add (sz : Size) (d n m : Reg)
  /-- `add d, n, #imm` (ADD (immediate), `imm < 4096`, no shift) -/
  | addImm (sz : Size) (d n : Reg) (imm : Nat)
  /-- `sub d, n, #imm` (SUB (immediate), `imm < 4096`, no shift) -/
  | subImm (sz : Size) (d n : Reg) (imm : Nat)
  /-- `and`/`orr`/`eor d, n, m` (shifted register, no shift) -/
  | logic (op : LogicOp) (sz : Size) (d n m : Reg)
  /-- `ror d, n, #sh` (alias of EXTR d, n, n, #sh), `sh < size` -/
  | ror (sz : Size) (d n : Reg) (sh : Nat)
  /-- `lsr d, n, #sh` (alias of UBFM), `sh < size` -/
  | lsr (sz : Size) (d n : Reg) (sh : Nat)
  /-- `rev wd, wn` (REV, 32-bit): reverse the bytes of the low 32 bits -/
  | rev32 (d n : Reg)
  /-- `movz d, #imm, lsl #(16 * hw)` -/
  | movz (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `movk d, #imm, lsl #(16 * hw)` -/
  | movk (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `ldr t, [n, #off]` (LDR (immediate), unsigned offset: a multiple of the
  access size, less than 4096 times it) -/
  | ldr (sz : Size) (t n : Reg) (off : Nat)
  /-- `str t, [n, #off]` (STR (immediate), unsigned offset, as for `ldr`) -/
  | str (sz : Size) (t n : Reg) (off : Nat)
  deriving DecidableEq, Repr

/-- Branch conditions. -/
inductive Cond
  /-- `cbz r, …`: the register (of the given size) is zero -/
  | zero (sz : Size) (r : Reg)
  /-- `cbnz r, …`: the register (of the given size) is not zero -/
  | nonzero (sz : Size) (r : Reg)
  deriving DecidableEq, Repr

namespace State

/-- Read a register at the operand size (`W[n]` or `X[n]`). -/
def read (s : State) (sz : Size) (r : Reg) : BitVec sz.bits := (s.gpr r).setWidth sz.bits

/-- Write a register at the operand size, zero-extending a 32-bit value. -/
def write (s : State) (sz : Size) (r : Reg) (v : BitVec sz.bits) : State :=
  { s with gpr := fun r' => if r' = r then v.setWidth 64 else s.gpr r' }

/-- Load `n` bytes, faulting if not permitted. -/
def load (s : State) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  if InRegions (s.rd ++ s.wr) a n then some (s.mem.read a n) else none

/-- Store `n` bytes, faulting if not permitted. -/
def store (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Option State :=
  if InRegions s.wr a n then some { s with mem := s.mem.write a n v } else none

end State

abbrev Size.bytes : Size → Nat
  | .w => 4
  | .x => 8

theorem Size.bits_eq (sz : Size) : sz.bits = 8 * sz.bytes := by cases sz <;> rfl

/-- The address of `[n, #off]`, if `off` is encodable (DDI 0487 C6.2, "LDR
(immediate)"/"STR (immediate)", unsigned offset: `offset = LSL(imm12, scale)`). -/
def addr (s : State) (sz : Size) (n : Reg) (off : Nat) : Option Addr :=
  if off % sz.bytes = 0 ∧ off < 4096 * sz.bytes then some (s.gpr n + BitVec.ofNat 64 off)
  else none

/-- `REV` (32-bit): `result<7:0> = X<31:24>` etc. (DDI 0487 C6.2, "REV"). -/
def rev32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- Semantics, transcribing DDI 0487 C6.2:
* "ADD (shifted register)", "ADD (immediate)", "SUB (immediate)": the
  result of `AddWithCarry` (the flags are not set by these forms);
* "AND/ORR/EOR (shifted register)";
* "ROR (immediate)" = "EXTR" with both sources `n`: `(n:n)<sh+size-1:sh>`,
  a rotation right by `sh`;
* "LSR (immediate)" = "UBFM": a logical shift right by `sh`;
* "REV"; "MOVZ": `imm` at bit `16 * hw` of zeros; "MOVK": `imm` into bits
  `16 * hw + 15 : 16 * hw` of the destination, the others unchanged (`hw < 2`
  for 32-bit, `hw < 4` for 64-bit);
* "LDR (immediate)": the loaded value is zero-extended; "STR (immediate)":
  the low `size` bits are stored. -/
def exec : Instr → State → Option State
  | .add sz d n m, s => some (s.write sz d (s.read sz n + s.read sz m))
  | .addImm sz d n imm, s =>
    if imm < 4096 then some (s.write sz d (s.read sz n + BitVec.ofNat _ imm)) else none
  | .subImm sz d n imm, s =>
    if imm < 4096 then some (s.write sz d (s.read sz n - BitVec.ofNat _ imm)) else none
  | .logic op sz d n m, s =>
    let a := s.read sz n
    let b := s.read sz m
    some (s.write sz d (match op with | .and => a &&& b | .orr => a ||| b | .eor => a ^^^ b))
  | .ror sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d ((s.read sz n).rotateRight sh)) else none
  | .lsr sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d (s.read sz n >>> sh)) else none
  | .rev32 d n, s => some (s.write .w d (rev32 (s.read .w n)))
  | .movz sz d imm hw, s =>
    if 16 * hw < sz.bits then some (s.write sz d (imm.setWidth sz.bits <<< (16 * hw))) else none
  | .movk sz d imm hw, s =>
    if 16 * hw < sz.bits then
      let mask : BitVec sz.bits := (0xFFFF : BitVec sz.bits) <<< (16 * hw)
      some (s.write sz d ((s.read sz d &&& ~~~mask) ||| (imm.setWidth sz.bits <<< (16 * hw))))
    else none
  | .ldr sz t n off, s =>
    (addr s sz n off).bind fun a =>
      (s.load a sz.bytes).map fun v => s.write sz t (v.setWidth sz.bits)
  | .str sz t n off, s =>
    (addr s sz n off).bind fun a => s.store a sz.bytes ((s.read sz t).setWidth (8 * sz.bytes))

def addrs : Instr → State → List Addr
  | .ldr _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .str _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | _, _ => []

/-- DDI 0487 C6.2, "CBZ"/"CBNZ": the branch is taken iff the operand is (not) zero. -/
def eval : Cond → State → Option Bool
  | .zero sz r, s => some (s.read sz r == 0)
  | .nonzero sz r, s => some (s.read sz r != 0)

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval

end VG.AArch64

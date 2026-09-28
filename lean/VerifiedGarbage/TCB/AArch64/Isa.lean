import VerifiedGarbage.TCB.Code

/-!
# AArch64 machine model

**Trusted.** A model of the subset of AArch64 (A64) used by our
implementations. Each instruction's semantics here must agree with the Arm
Architecture Reference Manual for A-profile (DDI 0487), chapter C6 ("A64
Base Instruction Descriptions"); when adding an instruction, cite the section
whose pseudocode it transcribes.

Modelling choices:
* Registers are `x0`–`x17` and `x19`–`x30`. `x18` is not modelled, so no
  code can use it: it is the platform register (AAPCS64 §6.1.1, "r18 …
  The Platform Register, if needed; otherwise a temporary register", and
  "software developers creating platform-independent code are advised to
  avoid using r18 if at all possible"). Apple's platforms reserve it ("The
  platform reserves register x18. Don't use this register.", *Writing ARM64
  code for Apple platforms*) and Windows points it at the thread's TEB
  (*Overview of ARM64 ABI conventions*), so it may change under a function
  that writes it, and restoring it before returning is not enough.
* The stack pointer is separate and only the push
  and pop of a frame (`str`/`ldr` with writeback, see `push`) read or write
  it (register number 31, SP or the zero register, is never an operand).
  Each operand is a 32-bit (`w`) or a 64-bit (`x`) register; a 32-bit
  result is zero-extended into the 64-bit register (DDI 0487, the pseudocode
  accessor `X[n, width] = value` sets `_R[n] = ZeroExtend(value, 64)`).
* The condition flags are not modelled, and no modelled instruction reads or
  writes them; control flow uses `cbz`/`cbnz`.
* Immediates that the instruction cannot encode make the instruction fault,
  so verified code only ever contains encodable instructions.
* Memory accesses (32-bit, 64-bit, and single bytes via `ldrb`/`strb`) must
  lie within the state's permitted regions: loads within `rd ++ wr`, stores
  within `wr`; otherwise the instruction faults. Memory is little-endian.
* Instructions whose timing depends on their operands (e.g. `udiv`) must never
  be added: the constant-time leakage model assumes they do not exist. The
  multiplies (`madd`, `mul`) and the shifts (`lsl`, `lsr`: UBFM) are among the
  data-processing instructions that Arm specifies to take a time independent
  of their data when PSTATE.DIT is 1 (DDI 0487, "About PSTATE.DIT", FEAT_DIT,
  which lists MADD and UBFM, as it does the other modelled data-processing
  instructions that read a register: ADD, SUB, AND, EOR, ORR, EXTR, REV and
  MOVK). The code does not set PSTATE.DIT, for these as for the others.
* Calls are `bl` and returns `ret` (DDI 0487, C6.2 "BL", "RET"). The return
  addresses are the next of the state's `unknowns`, which nothing constrains
  (see `TCB/Code.lean`). A linker veneer between a `bl` and its target may
  change `x16` and `x17` (IP0, IP1: AAPCS64 §6.1.1, "Use of IP0 and IP1 by
  the linker"), so a call leaves unknown values in them too.
* The stack pointer is always 16-byte aligned (AAPCS64 §6.4.5.1, "SP mod 16
  = 0"), and a frame moves it by 16 bytes, so the model does not check the
  stack alignment that the push and pop of a frame require.
-/

namespace VG.AArch64

inductive Reg
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x30
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
  /-- Values the model does not know, used in order: the return address each
  call stores and, on the ARM targets, what a linker veneer may leave in the
  intra-procedure-call scratch registers (see `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 64 := fun _ => 0

inductive LogicOp | and | orr | eor
  deriving DecidableEq, Repr

inductive Instr
  /-- `add d, n, m` (ADD (shifted register), no shift) -/
  | add (sz : Size) (d n m : Reg)
  /-- `sub d, n, m` (SUB (shifted register), no shift) -/
  | sub (sz : Size) (d n m : Reg)
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
  /-- `lsl d, n, #sh` (LSL (immediate), alias of UBFM), `sh < size` -/
  | lsl (sz : Size) (d n : Reg) (sh : Nat)
  /-- `madd d, n, m, a` (MADD): `a + n * m`, modulo `2 ^ size` -/
  | madd (sz : Size) (d n m a : Reg)
  /-- `mul d, n, m` (MUL, the alias of MADD with the zero register as the
  addend): `n * m`, modulo `2 ^ size` -/
  | mul (sz : Size) (d n m : Reg)
  /-- `rev wd, wn` (REV, 32-bit): reverse the bytes of the low 32 bits -/
  | rev32 (d n : Reg)
  /-- `rev xd, xn` (REV, 64-bit): reverse the bytes of all 64 bits -/
  | rev (d n : Reg)
  /-- `movz d, #imm, lsl #(16 * hw)` -/
  | movz (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `movk d, #imm, lsl #(16 * hw)` -/
  | movk (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `ldr t, [n, #off]` (LDR (immediate), unsigned offset: a multiple of the
  access size, less than 4096 times it) -/
  | ldr (sz : Size) (t n : Reg) (off : Nat)
  /-- `str t, [n, #off]` (STR (immediate), unsigned offset, as for `ldr`) -/
  | str (sz : Size) (t n : Reg) (off : Nat)
  /-- `ldrb wt, [n, #off]` (LDRB (immediate), unsigned offset, `off < 4096`):
  the byte, zero-extended into the 64-bit register -/
  | ldrb (t n : Reg) (off : Nat)
  /-- `strb wt, [n, #off]` (STRB (immediate), unsigned offset, `off < 4096`):
  the low byte of `t` -/
  | strb (t n : Reg) (off : Nat)
  /-- `str xr, [sp, #-16]!` (STR (immediate), 64-bit, pre-index): the push
  of a frame of 16 bytes (see `push`) -/
  | push (r : Reg)
  /-- `ldr xr, [sp], #16` (LDR (immediate), 64-bit, post-index): the pop of a
  frame of 16 bytes (see `pop`) -/
  | pop (r : Reg)
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

/-- The address of `[n, #off]` for an access of `bytes` bytes, if `off` is
encodable (DDI 0487 C6.2, "LDR (immediate)"/"STR (immediate)" and "LDRB
(immediate)"/"STRB (immediate)", unsigned offset: `offset = LSL(imm12,
scale)`, where `bytes = 2 ^ scale`, and `scale = 0` for the byte forms). -/
def addr (s : State) (bytes : Nat) (n : Reg) (off : Nat) : Option Addr :=
  if off % bytes = 0 ∧ off < 4096 * bytes then some (s.gpr n + BitVec.ofNat 64 off)
  else none

/-- `REV` (32-bit): `result<7:0> = X<31:24>` etc. (DDI 0487 C6.2, "REV"). -/
def rev32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- `REV` (64-bit): `Reverse(X[n, 64], 8)`, i.e. `result<7:0> = X<63:56>`,
`result<15:8> = X<55:48>`, …, `result<63:56> = X<7:0>` (DDI 0487 C6.2,
"REV"). -/
def rev64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

/-- Semantics, transcribing DDI 0487 C6.2:
* "ADD (shifted register)", "ADD (immediate)", "SUB (immediate)": the
  result of `AddWithCarry` (the flags are not set by these forms);
* "SUB (shifted register)": `AddWithCarry(operand1, NOT(operand2), '1')`,
  i.e. `n - m` modulo `2 ^ size` (the flags are not set by this form);
* "AND/ORR/EOR (shifted register)";
* "ROR (immediate)" = "EXTR" with both sources `n`: `(n:n)<sh+size-1:sh>`,
  a rotation right by `sh`;
* "LSR (immediate)" = "UBFM": a logical shift right by `sh`;
* "LSL (immediate)" = "UBFM" with `immr = -sh MOD size`, `imms = size - 1 -
  sh`: a logical shift left by `sh` (the bits shifted out are lost, zeros
  shifted in);
* "MADD": `result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
  X[d, destsize] = result<destsize-1:0>`, with `operand1 = X[n]`, `operand2
  = X[m]`, `operand3 = X[a]` at the operand size; "MUL" = "MADD" with `a` the
  zero register, so `operand3 = 0` (the flags are not set by either);
* "REV" (32- and 64-bit); "MOVZ": `imm` at bit `16 * hw` of zeros; "MOVK":
  `imm` into bits `16 * hw + 15 : 16 * hw` of the destination, the others
  unchanged (`hw < 2` for 32-bit, `hw < 4` for 64-bit);
* "LDR (immediate)": the loaded value is zero-extended; "STR (immediate)":
  the low `size` bits are stored;
* "LDRB (immediate)": `data = Mem[address, 1]; X[t, 32] = ZeroExtend(data,
  32)` (hence zero-extended to 64 bits); "STRB (immediate)": `data = X[t,
  8]; Mem[address, 1] = data`, the low byte of `t`. -/
def exec : Instr → State → Option State
  | .add sz d n m, s => some (s.write sz d (s.read sz n + s.read sz m))
  | .sub sz d n m, s => some (s.write sz d (s.read sz n - s.read sz m))
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
  | .lsl sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d (s.read sz n <<< sh)) else none
  | .madd sz d n m a, s => some (s.write sz d (s.read sz a + s.read sz n * s.read sz m))
  | .mul sz d n m, s => some (s.write sz d (s.read sz n * s.read sz m))
  | .rev32 d n, s => some (s.write .w d (rev32 (s.read .w n)))
  | .rev d n, s => some (s.write .x d (rev64 (s.read .x n)))
  | .movz sz d imm hw, s =>
    if 16 * hw < sz.bits then some (s.write sz d (imm.setWidth sz.bits <<< (16 * hw))) else none
  | .movk sz d imm hw, s =>
    if 16 * hw < sz.bits then
      let mask : BitVec sz.bits := (0xFFFF : BitVec sz.bits) <<< (16 * hw)
      some (s.write sz d ((s.read sz d &&& ~~~mask) ||| (imm.setWidth sz.bits <<< (16 * hw))))
    else none
  | .ldr sz t n off, s =>
    (addr s sz.bytes n off).bind fun a =>
      (s.load a sz.bytes).map fun v => s.write sz t (v.setWidth sz.bits)
  | .str sz t n off, s =>
    (addr s sz.bytes n off).bind fun a => s.store a sz.bytes ((s.read sz t).setWidth (8 * sz.bytes))
  | .ldrb t n off, s =>
    (addr s 1 n off).bind fun a => (s.load a 1).map fun v => s.write .w t (v.setWidth 32)
  | .strb t n off, s =>
    (addr s 1 n off).bind fun a => s.store a 1 ((s.read .w t).setWidth 8)
  -- Only the push and pop of a frame (`push`, `pop`).
  | .push _, _ | .pop _, _ => none

def addrs : Instr → State → List Addr
  | .ldr _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .str _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .ldrb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .strb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .push _, s => [s.sp - 16]
  | .pop _, s => [s.sp]
  | _, _ => []

/-- DDI 0487 C6.2, "CBZ"/"CBNZ": the branch is taken iff the operand is (not) zero. -/
def eval : Cond → State → Option Bool
  | .zero sz r, s => some (s.read sz r == 0)
  | .nonzero sz r, s => some (s.read sz r != 0)

/-- DDI 0487, C6.2 "BL": `X[30, 64] = PC64 + 4` (the address of the next
instruction), then the branch, possibly through a linker veneer, which may
change `x16` and `x17` (AAPCS64 §6.1.1). The return address and the values
left in `x16` and `x17` are the next three of the state's. -/
def call (s : State) : Option State :=
  some { s with
    gpr := fun r =>
      if r = .x30 then s.unknowns 0 else if r = .x16 then s.unknowns 1
      else if r = .x17 then s.unknowns 2 else s.gpr r
    unknowns := fun n => s.unknowns (n + 3) }

/-- DDI 0487, C6.2 "RET" (with the default register `x30`): `target =
X[30, 64]; BranchTo(target)`. It returns after the call instruction if `x30`
is the return address the call left (`s₁`); otherwise the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .x30 = s₁.gpr .x30 then some s₂ else none

/-- The push of a frame, DDI 0487 C6.2 "STR (immediate)", 64-bit, pre-index
(`str xr, [sp, #-16]!`): `address = SP[] + offset` with `offset = -16`;
`Mem[address, 8] = X[t]`; `SP[] = address`. The 16 bytes (the register,
then 8 bytes it does not write) become a writable region, at the head of
`wr`. Faults if the frame would wrap around the address space
(`sp < 16`). -/
def push : Instr → State → Option State
  | .push r, s =>
    if 16 ≤ s.sp.toNat then
      let sp := s.sp - 16
      some { s with sp := sp, mem := s.mem.write sp 8 (s.gpr r), wr := ⟨sp, 16⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame, DDI 0487 C6.2 "LDR (immediate)", 64-bit, post-index
(`ldr xr, [sp], #16`): `address = SP[]`; `data = Mem[address, 8]`; `SP[] =
address + 16`; `X[t] = data`. Faults unless the stack pointer and the
writable regions are those the push left (`s₁`), whose head is the frame;
it removes the frame. -/
def pop : Instr → State → State → Option State
  | .pop r, s₁, s₂ =>
    if s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp, 16⟩ then
      some { s₂.write .x r (s₂.mem.read s₂.sp 8) with sp := s₂.sp + 16, wr := s₂.wr.tail }
    else none
  | _, _, _ => none

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs _ := []
  ret := ret
  retAddrs _ := []
  -- No modelled instruction has the stack pointer as an operand, other than
  -- the push and pop of a frame.
  writesSp _ := false
  push := push
  pop := pop
  -- Every modelled instruction is in the ARMv8.0-A baseline.
  requires _ := []

end VG.AArch64

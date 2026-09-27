import VerifiedGarbage.TCB.Code

/-!
# ARMv7 machine model

**Trusted.** A model of the subset of 32-bit ARMv7-A used by our
implementations. Each instruction's semantics here must agree with the ARM
Architecture Reference Manual, ARMv7-A and ARMv7-R edition (DDI 0406C),
chapter A8 ("Instruction Details"); when adding an instruction, cite the
section whose pseudocode it transcribes.

Modelling choices:
* Only instructions that exist, with the same semantics, in both the ARM
  (A32) and the Thumb (T32) instruction sets are modelled, so the model is
  right whichever of the two a function is assembled in.
* Registers are `r0`–`r12` and `lr` (`r14`); `sp` is separate: no modelled
  instruction writes it, and only `ldr t, [sp, #off]` (for arguments passed
  on the stack) reads it; `pc` is not an operand.
* Only the N, Z, C and V flags are modelled.
* Immediates that an A32 instruction cannot encode make the instruction
  fault, so verified code only contains encodable instructions. (A T32
  encoding exists for fewer modified immediates; one that is missing is an
  assembler error, not a different meaning.) Shift amounts are `1`–`31`.
* Addresses are 32 bits (computed modulo 2³²) and zero-extended to the 64-bit
  addresses of `Mem`. Memory accesses must lie within the state's permitted
  regions: loads within `rd ++ wr`, stores within `wr`; otherwise the
  instruction faults. Memory is little-endian.
* Instructions whose timing depends on their operands (e.g. `sdiv`, `udiv`)
  must never be added: the constant-time leakage model assumes they do not
  exist.
-/

namespace VG.Arm

inductive Reg
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | lr
  deriving DecidableEq, Repr, Inhabited

structure State where
  gpr : Reg → BitVec 32
  sp : BitVec 32
  /-- The N, Z, C and V flags. -/
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region

inductive Shift | lsl | lsr | ror
  deriving DecidableEq, Repr

/-- The second operand of a data-processing instruction. -/
inductive Op2
  /-- `#imm` -/
  | imm (v : BitVec 32)
  /-- `rm` -/
  | reg (r : Reg)
  /-- `rm, <shift> #amount` -/
  | shifted (r : Reg) (sh : Shift) (amount : Nat)
  deriving DecidableEq, Repr

inductive DpOp | add | sub | and | orr | eor
  deriving DecidableEq, Repr

inductive Instr
  /-- `mov d, op2` (with a shifted register, printed as the `lsl`/`lsr`/`ror`
  alias) -/
  | mov (d : Reg) (op2 : Op2)
  /-- `add`/`sub`/`and`/`orr`/`eor d, n, op2` (no flags set) -/
  | dp (op : DpOp) (d n : Reg) (op2 : Op2)
  /-- `subs d, n, op2` (sets N, Z, C, V) -/
  | subs (d n : Reg) (op2 : Op2)
  /-- `cmp n, op2` (sets N, Z, C, V) -/
  | cmp (n : Reg) (op2 : Op2)
  /-- `movw d, #imm16` -/
  | movw (d : Reg) (imm : BitVec 16)
  /-- `movt d, #imm16` -/
  | movt (d : Reg) (imm : BitVec 16)
  /-- `rev d, m` -/
  | rev (d m : Reg)
  /-- `ldr t, [n, #off]` (`0 ≤ off < 4096`) -/
  | ldr (t n : Reg) (off : Nat)
  /-- `str t, [n, #off]` (`0 ≤ off < 4096`) -/
  | str (t n : Reg) (off : Nat)
  /-- `ldrb t, [n, #off]` (`0 ≤ off < 4096`) -/
  | ldrb (t n : Reg) (off : Nat)
  /-- `strb t, [n, #off]` (`0 ≤ off < 4096`) -/
  | strb (t n : Reg) (off : Nat)
  /-- `ldr t, [sp, #off]` (`0 ≤ off < 4096`) -/
  | ldrSp (t : Reg) (off : Nat)
  deriving DecidableEq, Repr

/-- Branch conditions (`b<cond>`). -/
inductive Cond
  /-- `eq`: Z = 1 -/
  | eq
  /-- `ne`: Z = 0 -/
  | ne
  deriving DecidableEq, Repr

/-- DDI 0406C A5.2.4, "Modified immediate constants in ARM instructions": an
8-bit value rotated right by an even amount. -/
def encodable (v : BitVec 32) : Bool :=
  (List.range 16).any fun k => (v.rotateLeft (2 * k)).toNat < 256

namespace State

def setReg (s : State) (r : Reg) (x : BitVec 32) : State :=
  { s with gpr := fun r' => if r' = r then x else s.gpr r' }

/-- The 64-bit address of a 32-bit address. -/
def addr (a : BitVec 32) : Addr := a.setWidth 64

/-- Load 4 bytes, faulting if not permitted. -/
def load32 (s : State) (a : Addr) : Option (BitVec 32) :=
  if InRegions (s.rd ++ s.wr) a 4 then some (s.mem.readW a 32) else none

/-- Store 4 bytes, faulting if not permitted. -/
def store32 (s : State) (a : Addr) (x : BitVec 32) : Option State :=
  if InRegions s.wr a 4 then some { s with mem := s.mem.writeW a x } else none

/-- Load 1 byte, faulting if not permitted. -/
def load8 (s : State) (a : Addr) : Option (BitVec 8) :=
  if InRegions (s.rd ++ s.wr) a 1 then some (s.mem a) else none

/-- Store 1 byte, faulting if not permitted. -/
def store8 (s : State) (a : Addr) (x : BitVec 8) : Option State :=
  if InRegions s.wr a 1 then some { s with mem := s.mem.writeW a x } else none

end State

/-- The value of the second operand (DDI 0406C A8.4.3, `Shift_C`; the carry
out of the shifter is not modelled, as no modelled instruction uses it), or
`none` if it cannot be encoded. -/
def Op2.eval (s : State) : Op2 → Option (BitVec 32)
  | .imm v => if encodable v then some v else none
  | .reg r => some (s.gpr r)
  | .shifted r sh n =>
    if 1 ≤ n ∧ n ≤ 31 then
      some (match sh with
        | .lsl => s.gpr r <<< n
        | .lsr => s.gpr r >>> n
        | .ror => (s.gpr r).rotateRight n)
    else none

/-- The flags of `x - y` (DDI 0406C A2.2.1, `AddWithCarry(x, NOT(y), '1')`). -/
def subFlags (s : State) (x y : BitVec 32) : State :=
  let r := x - y
  { s with n := r.msb, z := r == 0, c := y.toNat ≤ x.toNat,
           v := x.msb != y.msb && r.msb != x.msb }

/-- `REV`: `result<31:24> = R[m]<7:0>` etc. (DDI 0406C A8.8.145). -/
def rev (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- Semantics, transcribing DDI 0406C A8.8: "MOV (immediate)", "MOV
(register)", "LSL/LSR/ROR (immediate)" (the aliases of MOV with a shifted
register); "ADD/SUB/AND/ORR/EOR (immediate)", "(register)" (with `S` = 0,
so no flags); "SUB (immediate/register)" with `S` = 1 and "CMP": N, Z, C, V
from `AddWithCarry(R[n], NOT(op2), '1')`; "MOVW" (`R[d] = ZeroExtend(imm16)`);
"MOVT" (`R[d]<31:16> = imm16`, the low half unchanged); "REV"; "LDR
(immediate)"/"STR (immediate)" with a positive offset and no writeback
(A8.8.63, A8.8.204), including "LDR (immediate)" with `n` = 13 (`sp`) for
arguments on the stack; "LDRB (immediate)" (A8.8.68: `R[t] =
ZeroExtend(MemU[address,1], 32)`) and "STRB (immediate)" (A8.8.207:
`MemU[address,1] = R[t]<7:0>`) with a positive offset and no writeback. -/
def exec : Instr → State → Option State
  | .mov d op2, s => (op2.eval s).map fun x => s.setReg d x
  | .dp op d n op2, s => (op2.eval s).map fun y =>
    let x := s.gpr n
    s.setReg d (match op with
      | .add => x + y | .sub => x - y | .and => x &&& y | .orr => x ||| y | .eor => x ^^^ y)
  | .subs d n op2, s => (op2.eval s).map fun y =>
    (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)
  | .cmp n op2, s => (op2.eval s).map fun y => subFlags s (s.gpr n) y
  | .movw d imm, s => some (s.setReg d (imm.setWidth 32))
  | .movt d imm, s => some (s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32))
  | .rev d m, s => some (s.setReg d (rev (s.gpr m)))
  | .ldr t n off, s =>
    if off < 4096 then
      (s.load32 (State.addr (s.gpr n + BitVec.ofNat 32 off))).map fun x => s.setReg t x
    else none
  | .str t n off, s =>
    if off < 4096 then s.store32 (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t)
    else none
  | .ldrb t n off, s =>
    if off < 4096 then
      (s.load8 (State.addr (s.gpr n + BitVec.ofNat 32 off))).map fun x => s.setReg t (x.setWidth 32)
    else none
  | .strb t n off, s =>
    if off < 4096 then s.store8 (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8)
    else none
  | .ldrSp t off, s =>
    if off < 4096 then
      (s.load32 (State.addr (s.sp + BitVec.ofNat 32 off))).map fun x => s.setReg t x
    else none

def addrs : Instr → State → List Addr
  | .ldr _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .str _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .ldrb _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .strb _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .ldrSp _ off, s => [State.addr (s.sp + BitVec.ofNat 32 off)]
  | _, _ => []

def eval : Cond → State → Option Bool
  | .eq, s => some s.z
  | .ne, s => some !s.z

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval

end VG.Arm

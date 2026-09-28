import VerifiedGarbage.TCB.Code

/-!
# 64-bit little-endian PowerPC machine model

**Trusted.** A model of the subset of the 64-bit Power ISA used by our
implementations, in little-endian mode. Each instruction's semantics here
must agree with the Power ISA, Version 3.1C (OpenPOWER Foundation), Book I
(chapter 2, "Branch Facility", and chapter 3, "Fixed-Point Facility"); when
adding an instruction, cite the section whose pseudocode (RTL) it
transcribes. The RTL numbers bits from 0 at the most significant end:
`(RS)32:63` is the low 32 bits of `RS`.

Modelling choices:
* Registers are `r0`, `r2`–`r12` and `r14`–`r31`. The stack pointer `r1` is
  separate and only the push and pop of a frame (see `push`) read or write
  it. `r13` is the thread pointer, which the ABI reserves (ELFv2 ABI §2.2.2.1,
  Table 2.21, "Reserved"): it is never an operand, so never changed. The link
  register `LR` is modelled (`State.lr`); the count register, `XER` and the
  condition register are not, and no modelled instruction reads them.
* The registers are 64 bits. The only 32-bit operations are the rotates and
  shifts of words (`rlwinm`, which reads the low 32 bits and zero-extends
  its 32-bit result), the loads of words (zero-extended), the stores of words
  (the low 32 bits) and the comparison of a word with zero; `add`, `subf`
  and the logical instructions always act on all 64 bits.
* In the forms that read `(RA|0)`, `RA = 0` means the value 0, not `r0`: the
  model has only `li` (`addi RT, 0, SI`) and `lis` (`addis RT, 0, SI`) of
  those, and every other such instruction with `r0` as its base (`RA`)
  faults, so verified code never uses them.
* Immediates and displacements that the instruction cannot encode make the
  instruction fault, so verified code only ever contains encodable
  instructions. Displacements are non-negative.
* A branch condition (`Cond`) is a comparison with zero into condition
  register field 0 followed by the conditional branch on it (`cmpldi`/`cmplwi`
  then `beq`/`bne`): `CR0` is volatile (ELFv2 ABI §2.2.2.1, "Condition
  Register Fields") and nothing else reads it.
* Memory accesses (bytes, words and doublewords) must lie within the state's
  permitted regions: loads within `rd ++ wr`, stores within `wr`; otherwise
  the instruction faults. In little-endian mode `MEM(EA, n)` is the `n`
  bytes at `EA` with the byte at `EA + n - 1` most significant (Book I §1.3.2,
  "Notation", `MEM(x, y)`), i.e. a little-endian read (`Mem.read`).
* Instructions whose timing depends on their operands (e.g. `divd`) must
  never be added: the constant-time leakage model assumes they do not exist.
* Calls are `bl` and returns `blr` (Book I §2.4, "Branch Instructions"). The
  return addresses are the next of the state's `unknowns`, which nothing
  constrains (see `TCB/Code.lean`). Linkage code the linker may put between
  a `bl` and its target (a long-branch stub) may change `r0`, `r11` and
  `r12` (ELFv2 ABI §2.2.2.1, "Optional Function Linkage": "a function cannot
  depend on the values of those registers that are optional in the function
  linkage (r0, r11, and r12) because they may be altered by interlibrary
  calls"), so a call leaves unknown values in them too. The linker only adds
  a stub that saves `r2` to the stack if a `nop` follows the `bl` (ELFv2 ABI
  §2.2.1, "Function Call Linkage Protocols"), which the printer never emits,
  so a call does not access memory.
* The stack pointer is always 16-byte aligned (ELFv2 ABI §2.2.3.1, "The
  stack shall be quadword aligned"), and a frame moves it by 48 bytes, so
  the model does not check the alignment.
-/

namespace VG.PPC64LE

inductive Reg
  | r0 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12
  | r14 | r15 | r16 | r17 | r18 | r19 | r20 | r21 | r22 | r23 | r24 | r25 | r26 | r27 | r28
  | r29 | r30 | r31
  deriving DecidableEq, Repr, Inhabited

/-- Operand size of the loads, stores, rotates, shifts and comparisons: a
word (32 bits) or a doubleword (64 bits). -/
inductive Size | w | d
  deriving DecidableEq, Repr

abbrev Size.bits : Size → Nat
  | .w => 32
  | .d => 64

abbrev Size.bytes : Size → Nat
  | .w => 4
  | .d => 8

structure State where
  gpr : Reg → BitVec 64
  /-- The link register. -/
  lr : BitVec 64
  /-- The stack pointer, `r1`. -/
  sp : BitVec 64
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores and what linkage code may leave in `r0`, `r11` and `r12` (see
  `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 64 := fun _ => 0

inductive LogicOp | and | or | xor
  deriving DecidableEq, Repr

inductive Instr
  /-- `add RT, RA, RB` -/
  | add (d n m : Reg)
  /-- `subf RT, RB, RA` (extended mnemonic `sub RT, RA, RB`): `d := n - m` -/
  | sub (d n m : Reg)
  /-- `addi RT, RA, SI` with `0 ≤ SI < 2 ^ 15`, `RA ≠ 0` -/
  | addi (d n : Reg) (imm : Nat)
  /-- `addi RT, RA, -imm` (extended mnemonic `subi`), `0 ≤ imm ≤ 2 ^ 15`,
  `RA ≠ 0` -/
  | subi (d n : Reg) (imm : Nat)
  /-- `li RT, SI` (`addi RT, 0, SI`), `0 ≤ SI < 2 ^ 15` -/
  | li (d : Reg) (imm : Nat)
  /-- `lis RT, SI` (`addis RT, 0, SI`) -/
  | lis (d : Reg) (imm : BitVec 16)
  /-- `ori RA, RS, UI` -/
  | ori (d n : Reg) (imm : BitVec 16)
  /-- `oris RA, RS, UI` -/
  | oris (d n : Reg) (imm : BitVec 16)
  /-- `and`/`or`/`xor RA, RS, RB` -/
  | logic (op : LogicOp) (d n m : Reg)
  /-- A rotation right by `sh < size`: `rlwinm RA, RS, (32 - sh) % 32, 0, 31`
  (extended mnemonic `rotrwi`) for a word, `rldicl RA, RS, (64 - sh) % 64, 0`
  (`rotrdi`) for a doubleword -/
  | rotr (sz : Size) (d n : Reg) (sh : Nat)
  /-- A logical shift right by `sh < size`: `rlwinm RA, RS, (32 - sh) % 32,
  sh, 31` (extended mnemonic `srwi`) for a word, `rldicl RA, RS, (64 - sh) %
  64, sh` (`srdi`) for a doubleword -/
  | lsr (sz : Size) (d n : Reg) (sh : Nat)
  /-- A shift left of a doubleword by `sh < 64`: `rldicr RA, RS, sh, 63 - sh`
  (extended mnemonic `sldi`) -/
  | lsl (d n : Reg) (sh : Nat)
  /-- `lwz RT, D(RA)` (word, zero-extended) or `ld RT, DS(RA)` (doubleword,
  `DS` a multiple of 4), `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | load (sz : Size) (t n : Reg) (off : Nat)
  /-- `stw RS, D(RA)` (the low 32 bits) or `std RS, DS(RA)` (`DS` a multiple
  of 4), `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | store (sz : Size) (t n : Reg) (off : Nat)
  /-- `lbz RT, D(RA)`: the byte, zero-extended; `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | lbz (t n : Reg) (off : Nat)
  /-- `stb RS, D(RA)`: the low byte; `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | stb (t n : Reg) (off : Nat)
  /-- `lwbrx RT, RA, RB` (word, zero-extended) or `ldbrx RT, RA, RB`
  (doubleword): a load at `RA + RB` with the bytes reversed, i.e. big-endian;
  `RA ≠ 0` -/
  | loadRev (sz : Size) (t a b : Reg)
  /-- `stwbrx RS, RA, RB` (the low 32 bits) or `stdbrx RS, RA, RB`: a store at
  `RA + RB` with the bytes reversed, i.e. big-endian; `RA ≠ 0` -/
  | storeRev (sz : Size) (t a b : Reg)
  /-- `mflr RT` (`mfspr RT, 8`) -/
  | mflr (d : Reg)
  /-- `mtlr RS` (`mtspr 8, RS`) -/
  | mtlr (s : Reg)
  /-- `stdu r1, -48(r1)` then `std RS, 32(r1)`: the push of a frame of 48
  bytes (see `push`) -/
  | push (r : Reg)
  /-- `ld RT, 32(r1)` then `addi r1, r1, 48`: the pop of a frame of 48 bytes
  (see `pop`) -/
  | pop (r : Reg)
  deriving DecidableEq, Repr

/-- Branch conditions: a comparison with zero into `CR0`, then the branch. -/
inductive Cond
  /-- `cmplwi cr0, RA, 0` (word) or `cmpldi cr0, RA, 0` (doubleword), then
  `beq cr0, …`: the register (of the given size) is zero -/
  | zero (sz : Size) (r : Reg)
  /-- `cmplwi`/`cmpldi cr0, RA, 0`, then `bne cr0, …`: the register (of the
  given size) is not zero -/
  | nonzero (sz : Size) (r : Reg)
  deriving DecidableEq, Repr

namespace State

/-- A register at the operand size: the low 32 bits (`(RS)32:63`) of a word. -/
def read (s : State) (sz : Size) (r : Reg) : BitVec sz.bits := (s.gpr r).setWidth sz.bits

/-- Write all 64 bits of a register. -/
def write (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with gpr := fun r' => if r' = r then v else s.gpr r' }

/-- Load `n` bytes, faulting if not permitted. -/
def load (s : State) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  if InRegions (s.rd ++ s.wr) a n then some (s.mem.read a n) else none

/-- Store `n` bytes, faulting if not permitted. -/
def store (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Option State :=
  if InRegions s.wr a n then some { s with mem := s.mem.write a n v } else none

end State

theorem Size.bits_eq (sz : Size) : sz.bits = 8 * sz.bytes := by cases sz <;> rfl

/-- The effective address `(RA) + D` of `D(RA)` for an access of `bytes`
bytes, if the displacement is encodable and `RA ≠ 0` (Book I §3.3.2, "Load
Word and Zero", `EA ← b + EXTS(D)` with `b ← (RA)`, and likewise for the
other D-form loads and stores; §3.3.2 "Load Doubleword" and §3.3.3 "Store
Doubleword", DS-form: `EA ← b + EXTS(DS || 0b00)`, so the displacement is a
multiple of 4). The displacement is non-negative here. -/
def addr (s : State) (bytes : Nat) (n : Reg) (off : Nat) : Option Addr :=
  if n ≠ .r0 ∧ off < 2 ^ 15 ∧ (bytes = 8 → off % 4 = 0) then some (s.gpr n + BitVec.ofNat 64 off)
  else none

/-- The effective address `(RA) + (RB)` of an X-form access, if `RA ≠ 0`
(Book I §3.3.5: `EA ← b + (RB)` with `b ← (RA)`). -/
def addrX (s : State) (a b : Reg) : Option Addr :=
  if a ≠ .r0 then some (s.gpr a + s.gpr b) else none

/-- Reverse the bytes of a word. -/
def rev32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- Reverse the bytes of a doubleword. -/
def rev64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

/-- The value `v` at the operand size, zero-extended into a register. -/
abbrev Size.ext (sz : Size) (v : BitVec sz.bits) : BitVec 64 := v.setWidth 64

/-- Semantics, transcribing the Power ISA 3.1C, Book I:
* §3.3.9 "Add" (`RT ← (RA) + (RB)`), "Subtract From" (`RT ← ¬(RA) + (RB)
  + 1`, i.e. `(RB) - (RA)`), "Add Immediate" (`RT ← (RA|0) + EXTS(SI)`; `li`
  is `addi RT, 0, SI`, `subi RT, RA, imm` is `addi RT, RA, -imm`), "Add
  Immediate Shifted" (`lis RT, SI` is `addis RT, 0, SI`: `RT ← EXTS(SI ||
  0x0000)`); the non-record, non-overflow forms, which set no other
  register;
* §3.3.13 "OR Immediate" (`RA ← (RS) | (48 0 || UI)`), "OR Immediate
  Shifted" (`RA ← (RS) | (32 0 || UI || 16 0)`), "AND", "OR", "XOR" (the
  non-record forms);
* §3.3.14.1 "Rotate Left Word Immediate then AND with Mask" (`r ←
  ROTL32((RS)32:63, SH)`, `m ← MASK(MB+32, ME+32)`, `RA ← r & m`, where
  `ROTL32(x, n)` rotates `x || x` left, so with `MB = 0` and `ME = 31`, `m`
  selects the low 32 bits and `RA` is the word rotated left by `SH`,
  zero-extended; rotating left by `(32 - sh) % 32` rotates right by `sh`;
  with `MB = sh`, `m` further clears the high `sh` bits of the word, which
  leaves the word shifted right by `sh`); "Rotate Left Doubleword Immediate
  then Clear Left" (`RA ← ROTL64((RS), SH) & MASK(MB, 63)`: with `MB = 0` a
  rotation, and a rotation left by `(64 - sh) % 64` is one right by `sh`;
  with `MB = sh`, the doubleword shifted right by `sh`); "Rotate Left
  Doubleword Immediate then Clear Right" (`RA ← ROTL64((RS), SH) & MASK(0,
  ME)`: with `ME = 63 - sh`, the doubleword shifted left by `sh`);
* §3.3.2 "Load Byte and Zero" (`RT ← 56 0 || MEM(EA, 1)`), "Load Word and
  Zero" (`RT ← 32 0 || MEM(EA, 4)`), "Load Doubleword" (`RT ← MEM(EA, 8)`);
  §3.3.3 "Store Byte" (`MEM(EA, 1) ← (RS)56:63`), "Store Word" (`MEM(EA, 4)
  ← (RS)32:63`), "Store Doubleword" (`MEM(EA, 8) ← (RS)`);
* §3.3.5 "Load Word Byte-Reverse Indexed" (`load_data ← MEM(EA, 4)`, `RT ←
  32 0 || load_data24:31 || load_data16:23 || load_data8:15 ||
  load_data0:7`), "Store Word Byte-Reverse Indexed" (`MEM(EA, 4) ←
  (RS)56:63 || (RS)48:55 || (RS)40:47 || (RS)32:39`); §3.3.5.1 "Load
  Doubleword Byte-Reverse Indexed" and "Store Doubleword Byte-Reverse
  Indexed", likewise for the eight bytes;
* §3.3.19 "Move From Special Purpose Register" (`mflr RT` is `mfspr RT, 8`:
  `RT ← LR`) and "Move To Special Purpose Register" (`mtlr RS` is `mtspr 8,
  RS`: `LR ← (RS)`). -/
def exec : Instr → State → Option State
  | .add d n m, s => some (s.write d (s.gpr n + s.gpr m))
  | .sub d n m, s => some (s.write d (s.gpr n - s.gpr m))
  | .addi d n imm, s =>
    if n ≠ .r0 ∧ imm < 2 ^ 15 then some (s.write d (s.gpr n + BitVec.ofNat 64 imm)) else none
  | .subi d n imm, s =>
    if n ≠ .r0 ∧ imm ≤ 2 ^ 15 then some (s.write d (s.gpr n - BitVec.ofNat 64 imm)) else none
  | .li d imm, s => if imm < 2 ^ 15 then some (s.write d (BitVec.ofNat 64 imm)) else none
  | .lis d imm, s => some (s.write d ((imm ++ (0 : BitVec 16)).signExtend 64))
  | .ori d n imm, s => some (s.write d (s.gpr n ||| imm.setWidth 64))
  | .oris d n imm, s => some (s.write d (s.gpr n ||| imm.setWidth 64 <<< 16))
  | .logic op d n m, s =>
    let a := s.gpr n
    let b := s.gpr m
    some (s.write d (match op with | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b))
  | .rotr sz d n sh, s =>
    if sh < sz.bits then some (s.write d (sz.ext ((s.read sz n).rotateRight sh))) else none
  | .lsr sz d n sh, s =>
    if sh < sz.bits then some (s.write d (sz.ext (s.read sz n >>> sh))) else none
  | .lsl d n sh, s => if sh < 64 then some (s.write d (s.gpr n <<< sh)) else none
  | .load sz t n off, s =>
    (addr s sz.bytes n off).bind fun a =>
      (s.load a sz.bytes).map fun v => s.write t (v.setWidth 64)
  | .store sz t n off, s =>
    (addr s sz.bytes n off).bind fun a => s.store a sz.bytes ((s.gpr t).setWidth (8 * sz.bytes))
  | .lbz t n off, s =>
    (addr s 1 n off).bind fun a => (s.load a 1).map fun v => s.write t (v.setWidth 64)
  | .stb t n off, s =>
    (addr s 1 n off).bind fun a => s.store a 1 ((s.gpr t).setWidth 8)
  | .loadRev .w t a b, s =>
    (addrX s a b).bind fun ea => (s.load ea 4).map fun v => s.write t ((rev32 v).setWidth 64)
  | .loadRev .d t a b, s =>
    (addrX s a b).bind fun ea => (s.load ea 8).map fun v => s.write t (rev64 v)
  | .storeRev .w t a b, s =>
    (addrX s a b).bind fun ea => s.store ea 4 (rev32 (s.read .w t))
  | .storeRev .d t a b, s =>
    (addrX s a b).bind fun ea => s.store ea 8 (rev64 (s.gpr t))
  | .mflr d, s => some (s.write d s.lr)
  | .mtlr r, s => some { s with lr := s.gpr r }
  -- Only the push and pop of a frame (`push`, `pop`).
  | .push _, _ | .pop _, _ => none

def addrs : Instr → State → List Addr
  | .load _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .store _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .lbz _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .stb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .loadRev _ _ a b, s => [s.gpr a + s.gpr b]
  | .storeRev _ _ a b, s => [s.gpr a + s.gpr b]
  | .push _, s => [s.sp - 48, s.sp - 16]
  | .pop _, s => [s.sp + 32]
  | _, _ => []

/-- Book I §3.3.10 "Compare Logical Immediate" (`cmplwi` is `cmpli BF, 0,
RA, UI` and `cmpldi` is `cmpli BF, 1, RA, UI`): with `UI = 0`, `CR0`'s EQ bit
is set iff `(RA)32:63` (`L = 0`), or `(RA)` (`L = 1`), is zero; §2.4 "Branch
Conditional" (`beq cr0, …` is `bc 12, 2, …` and `bne cr0, …` is `bc 4, 2,
…`): the branch is taken iff that bit is set (`beq`) or clear (`bne`). -/
def eval : Cond → State → Option Bool
  | .zero sz r, s => some (s.read sz r == 0)
  | .nonzero sz r, s => some (s.read sz r != 0)

/-- Book I §2.4, "Branch" (`bl target` is `b` with `LK = 1`): `LR ← CIA +
4` (the address of the next instruction), then the branch, possibly
through linkage code, which may change `r0`, `r11` and `r12` (ELFv2 ABI
§2.2.2.1, "Optional Function Linkage"). The return address and the values
left in `r0`, `r11` and `r12` are the next four of the state's. -/
def call (s : State) : Option State :=
  some { s with
    lr := s.unknowns 0
    gpr := fun r =>
      if r = .r0 then s.unknowns 1 else if r = .r11 then s.unknowns 2
      else if r = .r12 then s.unknowns 3 else s.gpr r
    unknowns := fun n => s.unknowns (n + 4) }

/-- Book I §2.4, "Branch Conditional to Link Register" (`blr` is `bclr 20,
0`: branch always, `NIA ← LR0:61 || 0b00`). It returns after the call
instruction if `LR` is the return address the call left (`s₁`); otherwise
the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.lr = s₁.lr then some s₂ else none

/-- The push of a frame: Book I §3.3.3, "Store Doubleword with Update"
(`stdu r1, -48(r1)`: `EA ← (RA) + EXTS(DS || 0b00)`, `MEM(EA, 8) ← (RS)`,
`RA ← EA`, so the stack pointer moves down by 48 and the old stack pointer,
the back chain, is stored at the new one), then "Store Doubleword" (`std
RS, 32(r1)`). The frame is the minimum frame of the ELFv2 ABI (§2.2.3.1:
32 bytes, the back chain, the CR save word, a reserved word, the LR save
doubleword and the TOC pointer doubleword) followed by 16 bytes of local
variable space, which holds the register (and 8 bytes it does not write)
and becomes a writable region, at the head of `wr`. Faults if the frame
would wrap around the address space (`sp < 48`). -/
def push : Instr → State → Option State
  | .push r, s =>
    if 48 ≤ s.sp.toNat then
      let sp := s.sp - 48
      some { s with sp := sp, mem := (s.mem.write sp 8 s.sp).write (sp + 32) 8 (s.gpr r),
                    wr := ⟨sp + 32, 16⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame: Book I §3.3.2, "Load Doubleword" (`ld RT, 32(r1)`:
`RT ← MEM((r1) + 32, 8)`), then "Add Immediate" (`addi r1, r1, 48`). Faults
unless the stack pointer and the writable regions are those the push left
(`s₁`), whose head is the frame's local variable space; it removes that
region. -/
def pop : Instr → State → State → Option State
  | .pop r, s₁, s₂ =>
    if s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp + 32, 16⟩ then
      some { s₂.write r (s₂.mem.read (s₂.sp + 32) 8) with sp := s₂.sp + 48, wr := s₂.wr.tail }
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
  -- Every modelled instruction is in Power ISA 2.07 (POWER8), the baseline of
  -- `powerpc64le-unknown-linux-gnu`.
  requires _ := []

end VG.PPC64LE

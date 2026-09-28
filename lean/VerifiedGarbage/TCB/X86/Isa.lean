import VerifiedGarbage.TCB.Code

/-!
# x86 (32-bit) machine model

**Trusted.** A model of the subset of 32-bit x86 (IA-32, protected mode with
32-bit operand and address size) used by our implementations. Each
instruction's semantics here must agree with the Intel SDM; when adding an
instruction, cite the SDM pseudocode it transcribes.

Modelling choices:
* Registers are the eight 32-bit general-purpose registers. `esp` can be read
  (e.g. to address the arguments on the stack) like any other register.
* Operands are 32 bits wide, apart from byte loads (`movzx`, zero-extending)
  and byte stores. Without a REX prefix (unavailable outside 64-bit mode),
  only `al`, `cl`, `dl` and `bl` can be the source of a byte store as the low
  byte of a 32-bit register (SDM Vol. 1 §3.4.1.1 and Vol. 2 §3.1.1.1), so a
  byte store takes a `Reg8`.
* Only CF, ZF, SF and OF are modelled. Each is an `Option Bool`; `none` means
  "undefined" (as the SDM specifies for some instructions). Evaluating a
  branch on an undefined flag faults, so verified code never depends on one.
  PF and AF are not modelled, and no modelled instruction reads them.
* Effective addresses are computed modulo 2³² and zero-extended to the 64-bit
  addresses of `Mem` (segment bases are zero: the flat memory model of every
  mainstream 32-bit OS). Memory accesses must lie within the state's permitted
  regions: loads within `rd ++ wr`, stores within `wr`; otherwise the
  instruction faults. Memory is little-endian.
* The baseline is i686 as Rust's `i686-*` targets define it: a Pentium 4 or
  later, with SSE2 (the Rust crate refuses to build for 32-bit x86 without
  SSE2). Older CPUs are not supported: the 80386 and 80486 multiply in a
  time that depends on the multiplier (Intel 80386 Programmer's Reference
  Manual, "MUL": "an early-out multiply algorithm").
* Instructions whose timing depends on their operands (e.g. `div`) must never
  be added: the constant-time leakage model assumes they do not exist. `mul`
  is one of the instructions whose timing Intel documents as independent of
  their data operands on its Core and Atom processors ("Data Operand
  Independent Timing Instruction Set Architecture (ISA) Guidance", which
  lists `MUL`).
* Calls (`call`) and returns (`ret`) are near and direct (SDM Vol. 2, "CALL",
  "RET"). The return addresses are the next of the state's `unknowns`,
  which nothing constrains (see `TCB/Code.lean`).
* `push` and `pop` (of registers other than `esp`) only occur as the push
  and pop of a frame (see `push`), as a sequence of them.
-/

namespace VG.X86

inductive Reg
  | eax | ecx | edx | ebx | esp | ebp | esi | edi
  deriving DecidableEq, Repr, Inhabited

structure State where
  gpr : Reg → BitVec 32
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores and, on the ARM targets, what a linker veneer may leave in the
  intra-procedure-call scratch registers (see `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 32 := fun _ => 0

/-- A memory operand `[base + disp]`. -/
structure MemOp where
  base : Reg
  disp : Nat := 0
  deriving DecidableEq, Repr

/-- The registers whose low byte has an 8-bit name without a REX prefix:
`al`, `cl`, `dl`, `bl` (the low bytes of `eax`, `ecx`, `edx`, `ebx`). -/
inductive Reg8
  | al | cl | dl | bl
  deriving DecidableEq, Repr

/-- The 32-bit register whose low byte a `Reg8` is. -/
def Reg8.reg : Reg8 → Reg
  | .al => .eax | .cl => .ecx | .dl => .edx | .bl => .ebx

inductive Src
  | reg (r : Reg)
  | imm (v : BitVec 32)
  | mem (m : MemOp)
  deriving DecidableEq, Repr

inductive AluOp | add | adc | sub | sbb | and | or | xor | cmp | test
  deriving DecidableEq, Repr

inductive ShiftOp | ror | shr
  deriving DecidableEq, Repr

inductive Instr
  /-- `mov dst, src` -/
  | mov (dst : Reg) (src : Src)
  /-- `mov DWORD PTR [dst], src` -/
  | store (dst : MemOp) (src : Reg)
  /-- Two-operand ALU instruction `op dst, src`. -/
  | alu (op : AluOp) (dst : Reg) (src : Src)
  /-- `op dst, count` with an immediate count. Only counts `1 ≤ count ≤ 31` are
  modelled; any other count faults. -/
  | shift (op : ShiftOp) (dst : Reg) (count : Nat)
  /-- `bswap dst` -/
  | bswap (dst : Reg)
  /-- `movzx dst, BYTE PTR [src]`: the byte, zero-extended. -/
  | movzx8 (dst : Reg) (src : MemOp)
  /-- `mov BYTE PTR [dst], src`: the low byte of `src.reg`. -/
  | store8 (dst : MemOp) (src : Reg8)
  /-- `push r` for each `r` of `rs`, in order: the push of a frame (see
  `push`); `rs` must not be empty or contain `esp` -/
  | push (rs : List Reg)
  /-- `pop r`, `k` times: the pop of a frame of `4 * k` bytes (see `pop`);
  `k > 0`, and `r` is not `esp` -/
  | pop (r : Reg) (k : Nat)
  /-- `mul r32` (F7 /4): the unsigned product `EDX:EAX := EAX * r32`. -/
  | mul (src : Reg)
  deriving DecidableEq, Repr

/-- Branch conditions (`jcc` suffixes). -/
inductive Cond
  /-- `je`: ZF = 1 -/
  | e
  /-- `jne`: ZF = 0 -/
  | ne
  /-- `jb`: CF = 1 -/
  | b
  /-- `jae`: CF = 0 -/
  | ae
  deriving DecidableEq, Repr

namespace State

def setReg (s : State) (r : Reg) (v : BitVec 32) : State :=
  { s with gpr := fun r' => if r' = r then v else s.gpr r' }

/-- Effective address of a memory operand (32-bit, zero-extended). -/
def ea (s : State) (m : MemOp) : Addr := (s.gpr m.base + BitVec.ofNat 32 m.disp).setWidth 64

/-- Load 4 bytes, faulting if not permitted. -/
def load32 (s : State) (a : Addr) : Option (BitVec 32) :=
  if InRegions (s.rd ++ s.wr) a 4 then some (s.mem.readW a 32) else none

/-- Store 4 bytes, faulting if not permitted. -/
def store32 (s : State) (a : Addr) (v : BitVec 32) : Option State :=
  if InRegions s.wr a 4 then some { s with mem := s.mem.writeW a v } else none

/-- Load 1 byte, faulting if not permitted. -/
def load8 (s : State) (a : Addr) : Option Byte :=
  if InRegions (s.rd ++ s.wr) a 1 then some (s.mem a) else none

/-- Store 1 byte, faulting if not permitted. -/
def store8 (s : State) (a : Addr) (v : Byte) : Option State :=
  if InRegions s.wr a 1 then some { s with mem := s.mem.writeW a v } else none

/-- Set CF, OF, ZF and SF. -/
def setFlags (s : State) (cf of zf sf : Option Bool) : State :=
  { s with cf := cf, of := of, zf := zf, sf := sf }

end State

def readSrc (s : State) : Src → Option (BitVec 32)
  | .reg r => some (s.gpr r)
  | .imm v => some v
  | .mem m => s.load32 (s.ea m)

def srcAddrs (s : State) : Src → List Addr
  | .mem m => [s.ea m]
  | _ => []

/-- Flags after the result `r` of an arithmetic or logic operation with carry
`c` and signed overflow `o`: ZF and SF are computed from `r`. -/
def arithFlags (s : State) (r : BitVec 32) (c o : Bool) : State :=
  s.setFlags (some c) (some o) (some (r == 0)) (some r.msb)

/-- Signed overflow of `a + b (+ carry) = r`. -/
def addOverflow (a b r : BitVec 32) : Bool := a.msb == b.msb && r.msb != a.msb
/-- Signed overflow of `a - b (- borrow) = r`. -/
def subOverflow (a b r : BitVec 32) : Bool := a.msb != b.msb && r.msb != a.msb

/-- SDM Vol. 2: ADD, ADC, SUB, SBB, CMP set CF/OF/ZF/SF by the result; AND,
OR, XOR, TEST clear CF and OF and set ZF/SF by the result. CMP and TEST write
no register. -/
def execAlu (op : AluOp) (dst : Reg) (src : Src) (s : State) : Option State :=
  (readSrc s src).bind fun b =>
  let a := s.gpr dst
  match op with
  | .add => let r := a + b
    some ((arithFlags s r (2 ^ 32 ≤ a.toNat + b.toNat) (addOverflow a b r)).setReg dst r)
  | .adc => s.cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth 32
    (arithFlags s r (2 ^ 32 ≤ a.toNat + b.toNat + c.toNat) (addOverflow a b r)).setReg dst r
  | .sub => let r := a - b
    some ((arithFlags s r (a.toNat < b.toNat) (subOverflow a b r)).setReg dst r)
  | .sbb => s.cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth 32
    (arithFlags s r (a.toNat < b.toNat + c.toNat) (subOverflow a b r)).setReg dst r
  | .cmp => let r := a - b
    some (arithFlags s r (a.toNat < b.toNat) (subOverflow a b r))
  | .and => let r := a &&& b; some ((arithFlags s r false false).setReg dst r)
  | .or => let r := a ||| b; some ((arithFlags s r false false).setReg dst r)
  | .xor => let r := a ^^^ b; some ((arithFlags s r false false).setReg dst r)
  | .test => let r := a &&& b; some (arithFlags s r false false)

/-- SDM Vol. 2, "RCL/RCR/ROL/ROR" and "SAL/SAR/SHL/SHR", for a 32-bit
operand and a count `n` with `1 ≤ n ≤ 31` (so the masked count `n AND 1FH`
is `n`; other counts fault):

* ROR: the operand is rotated right by `n`; CF := MSB of the result; OF :=
  MSB XOR MSB−1 of the result if `n = 1`, otherwise undefined; SF and ZF are
  unaffected.
* SHR: the operand is shifted right (logically) by `n`; CF := the last bit
  shifted out (bit `n − 1` of the operand); OF := MSB of the original operand
  if `n = 1`, otherwise undefined; SF and ZF are set according to the result.

(AF and PF are not modelled.) -/
def execShift (op : ShiftOp) (dst : Reg) (n : Nat) (s : State) : Option State :=
  if 1 ≤ n ∧ n ≤ 31 then
    let a := s.gpr dst
    match op with
    | .ror => let r := a.rotateRight n
      some ((s.setFlags (some r.msb) (if n = 1 then some (r.msb ^^ r.getMsbD 1) else none)
        s.zf s.sf).setReg dst r)
    | .shr => let r := a >>> n
      some ((s.setFlags (some (a.getLsbD (n - 1))) (if n = 1 then some a.msb else none)
        (some (r == 0)) (some r.msb)).setReg dst r)
  else none

/-- SDM Vol. 2, "BSWAP": `DEST[7:0] := TEMP[31:24]; DEST[15:8] := TEMP[23:16];
DEST[23:16] := TEMP[15:8]; DEST[31:24] := TEMP[7:0]`. No flags are affected. -/
def bswap (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- SDM Vol. 2, "MUL—Unsigned Multiply", for a 32-bit operand: `EDX:EAX :=
EAX ∗ SRC` (the 64-bit product of the unsigned operands, its high half in
EDX and its low half in EAX). "The OF and CF flags are set to 0 if the upper
half of the result is 0; otherwise, they are set to 1. The SF, ZF, AF, and PF
flags are undefined." (AF and PF are not modelled.) -/
def execMul (src : Reg) (s : State) : State :=
  let p := (s.gpr .eax).toNat * (s.gpr src).toNat
  let hi : BitVec 32 := BitVec.ofNat 32 (p / 2 ^ 32)
  ((s.setFlags (some (hi != 0)) (some (hi != 0)) none none).setReg .eax (BitVec.ofNat 32 p)).setReg
    .edx hi

/-- Semantics of an instruction. The byte forms: SDM Vol. 2, "MOVZX":
`DEST := ZeroExtend(SRC)`, and "MOV": `DEST := SRC`, where the source of a
byte store is the low byte of `eax`, `ecx`, `edx` or `ebx` (AL, CL, DL, BL;
SDM Vol. 1 §3.4.1.1). Neither affects the flags. -/
def exec : Instr → State → Option State
  | .mov d src, s => (readSrc s src).map fun v => s.setReg d v
  | .store m r, s => s.store32 (s.ea m) (s.gpr r)
  | .alu op d src, s => execAlu op d src s
  | .shift op d n, s => execShift op d n s
  | .bswap d, s => some (s.setReg d (bswap (s.gpr d)))
  | .movzx8 d m, s => (s.load8 (s.ea m)).map fun v => s.setReg d (v.setWidth 32)
  | .store8 m r, s => s.store8 (s.ea m) ((s.gpr r.reg).setWidth 8)
  | .mul r, s => some (execMul r s)
  -- Only the push and pop of a frame (`push`, `pop`).
  | .push _, _ | .pop .., _ => none

def addrs : Instr → State → List Addr
  | .mov _ src, s => srcAddrs s src
  | .store m _, s => [s.ea m]
  | .alu _ _ src, s => srcAddrs s src
  | .shift .., _ => []
  | .bswap _, _ => []
  | .movzx8 _ m, s => [s.ea m]
  | .store8 m _, s => [s.ea m]
  | .mul _, _ => []
  | .push rs, s => (List.range rs.length).map fun i =>
    (s.gpr .esp - BitVec.ofNat 32 (4 * (i + 1))).setWidth 64
  | .pop _ k, s => (List.range k).map fun i =>
    (s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64

/-- SDM Vol. 2, "Jcc": JE jumps if ZF = 1, JNE if ZF = 0, JB if CF = 1 and
JAE if CF = 0. -/
def eval : Cond → State → Option Bool
  | .e, s => s.zf
  | .ne, s => s.zf.map (!·)
  | .b, s => s.cf
  | .ae, s => s.cf.map (!·)

/-- SDM Vol. 2, "CALL", near call with a 32-bit operand size: `ESP := ESP −
4; Memory[ESP] := EIP` (`Push(EIP)`, where `EIP` is the address of the next
instruction), then the jump. No flags are affected. The return address is
the next of the state's. -/
def call (s : State) : Option State :=
  let sp := s.gpr .esp - 4
  some { s.setReg .esp sp with
    mem := s.mem.writeW (sp.setWidth 64) (s.unknowns 0)
    unknowns := fun n => s.unknowns (n + 1) }

/-- SDM Vol. 2, "RET", near return with a 32-bit operand size: `EIP :=
Pop()`, i.e. `EIP := Memory[ESP]; ESP := ESP + 4`. No flags are affected. It
returns after the call instruction if `ESP` and the return address at
`[ESP]` are those the call left (`s₁`); otherwise the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .esp = s₁.gpr .esp ∧
      s₂.mem.readW ((s₂.gpr .esp).setWidth 64) 32 = s₁.mem.readW ((s₁.gpr .esp).setWidth 64) 32 then
    some (s₂.setReg .esp (s₂.gpr .esp + 4))
  else none

/-- `push r` for each of `rs`, in order, where `r ≠ esp`: SDM Vol. 2,
"PUSH", 32-bit operand size: `ESP := ESP − 4; Memory[SS:ESP] := SRC`. No
flags are affected. -/
def pushRegs (s : State) : List Reg → State
  | [] => s
  | r :: rs =>
    let sp := s.gpr .esp - 4
    pushRegs { s.setReg .esp sp with mem := s.mem.writeW (sp.setWidth 64) (s.gpr r) } rs

/-- `pop r`, `k` times, where `r ≠ esp`: SDM Vol. 2, "POP", 32-bit operand
size: `DEST := SS:ESP; ESP := ESP + 4`. No flags are affected. -/
def popReg (s : State) (r : Reg) : Nat → State
  | 0 => s
  | k + 1 =>
    popReg ((s.setReg r (s.mem.readW ((s.gpr .esp).setWidth 64) 32)).setReg .esp
      (s.gpr .esp + 4)) r k

/-- The push of a frame: `push r` for each `r` of `rs` (`pushRegs`). The
`4 * rs.length` bytes it stores become a writable region, at the head of
`wr`. Faults if `rs` is empty or contains `esp`, or if the frame would wrap
around the address space. -/
def push : Instr → State → Option State
  | .push rs, s =>
    let n := 4 * rs.length
    if rs ≠ [] ∧ .esp ∉ rs ∧ n ≤ (s.gpr .esp).toNat then
      some { pushRegs s rs with
        wr := ⟨(s.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame: `pop r`, `k` times (`popReg`), so that `r` holds the
last word of the frame. Faults if `k = 0` or `r` is `esp`, and unless `esp`
and the writable regions are those the push left (`s₁`), and the frame, the
region at their head, has `4 * k` bytes; it removes the frame. -/
def pop : Instr → State → State → Option State
  | .pop r k, s₁, s₂ =>
    if k ≠ 0 ∧ r ≠ .esp ∧ s₂.gpr .esp = s₁.gpr .esp ∧ s₂.wr = s₁.wr ∧
        s₁.wr.head? = some ⟨(s₁.gpr .esp).setWidth 64, 4 * k⟩ then
      some { popReg s₂ r k with wr := s₂.wr.tail }
    else none
  | _, _, _ => none

/-- The register an instruction writes, if it writes exactly one (the pop of
a frame also moves `esp`, as the push does): `mul` writes two, `eax` and
`edx`, and stores none. -/
def Instr.dst : Instr → Option Reg
  | .mov d _ | .alu _ d _ | .shift _ d _ | .bswap d | .movzx8 d _ | .pop d _ => some d
  | .store .. | .store8 .. | .push _ | .mul _ => none

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs s := [(s.gpr .esp - 4).setWidth 64]
  ret := ret
  retAddrs s := [(s.gpr .esp).setWidth 64]
  -- Other than as the push and pop of a frame. `mul` writes `eax` and `edx`,
  -- never `esp`.
  writesSp i := i.dst == some .esp
  push := push
  pop := pop
  -- Every modelled instruction is in the i686 baseline.
  requires _ := []

end VG.X86

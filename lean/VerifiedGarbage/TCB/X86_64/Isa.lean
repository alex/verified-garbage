import VerifiedGarbage.TCB.Code

/-!
# x86-64 machine model

**Trusted.** A model of the subset of x86-64 used by our implementations.
Each instruction's semantics here must agree with the Intel SDM; when adding
an instruction, cite the SDM pseudocode it transcribes.

Modelling choices:
* Only 64-bit operand size is modelled so far.
* Only CF, ZF, SF and OF are modelled. Each is an `Option Bool`; `none` means
  "undefined" (as the SDM specifies for some instructions). Evaluating a
  branch on an undefined flag faults, so verified code never depends on one.
  PF and AF are not modelled, and no modelled instruction reads them.
* Memory accesses must lie within the state's permitted regions: loads within
  `rd ++ wr`, stores within `wr`; otherwise the instruction faults.
* Instructions whose timing depends on their operands (e.g. `div`) must never
  be added: the constant-time leakage model assumes they do not exist.
-/

namespace VG.X86_64

inductive Reg
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

structure State where
  gpr : Reg → BitVec 64
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region

/-- A memory operand `[base + index * scale + disp]`. -/
structure MemOp where
  base : Reg
  index : Option Reg := none
  /-- 1, 2, 4 or 8. -/
  scale : Nat := 1
  disp : Int := 0
  deriving DecidableEq, Repr

inductive Src
  | reg (r : Reg)
  /-- A 32-bit immediate, sign-extended to 64 bits. -/
  | imm (v : BitVec 32)
  | mem (m : MemOp)
  deriving DecidableEq, Repr

inductive AluOp | add | adc | sub | sbb | and | or | xor | cmp | test
  deriving DecidableEq, Repr

inductive Instr
  /-- `mov dst, src` (64-bit) -/
  | mov (dst : Reg) (src : Src)
  /-- `mov QWORD PTR [dst], src` -/
  | store (dst : MemOp) (src : Reg)
  /-- Two-operand ALU instruction `op dst, src` (64-bit). -/
  | alu (op : AluOp) (dst : Reg) (src : Src)
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

def setReg (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with gpr := fun r' => if r' = r then v else s.gpr r' }

/-- Effective address of a memory operand. -/
def ea (s : State) (m : MemOp) : Addr :=
  match m.index with
  | none => s.gpr m.base + BitVec.ofInt 64 m.disp
  | some i => s.gpr m.base + s.gpr i * BitVec.ofNat 64 m.scale + BitVec.ofInt 64 m.disp

/-- Load 8 bytes, faulting if not permitted. -/
def load64 (s : State) (a : Addr) : Option (BitVec 64) :=
  if InRegions (s.rd ++ s.wr) a 8 then some (s.mem.readW a 64) else none

/-- Store 8 bytes, faulting if not permitted. -/
def store64 (s : State) (a : Addr) (v : BitVec 64) : Option State :=
  if InRegions s.wr a 8 then some { s with mem := s.mem.writeW a v } else none

/-- Set CF, OF, ZF and SF. -/
def setFlags (s : State) (cf of zf sf : Option Bool) : State :=
  { s with cf := cf, of := of, zf := zf, sf := sf }

end State

/-- Read a source operand. Immediates are sign-extended from 32 bits. -/
def readSrc (s : State) : Src → Option (BitVec 64)
  | .reg r => some (s.gpr r)
  | .imm v => some (v.signExtend 64)
  | .mem m => s.load64 (s.ea m)

def srcAddrs (s : State) : Src → List Addr
  | .mem m => [s.ea m]
  | _ => []

/-- Flags after the result `r` of an arithmetic or logic operation with carry
`c` and signed overflow `o`: ZF and SF are computed from `r`. -/
def arithFlags (s : State) (r : BitVec 64) (c o : Bool) : State :=
  s.setFlags (some c) (some o) (some (r == 0)) (some r.msb)

/-- Signed overflow of `a + b (+ carry) = r`. -/
def addOverflow (a b r : BitVec 64) : Bool := a.msb == b.msb && r.msb != a.msb
/-- Signed overflow of `a - b (- borrow) = r`. -/
def subOverflow (a b r : BitVec 64) : Bool := a.msb != b.msb && r.msb != a.msb

/-- SDM Vol. 2: ADD, ADC, SUB, SBB, CMP set CF/OF/ZF/SF by the result; AND,
OR, XOR, TEST clear CF and OF and set ZF/SF by the result. -/
def execAlu (op : AluOp) (dst : Reg) (src : Src) (s : State) : Option State :=
  (readSrc s src).bind fun b =>
  let a := s.gpr dst
  match op with
  | .add => let r := a + b
    some ((arithFlags s r (2 ^ 64 ≤ a.toNat + b.toNat) (addOverflow a b r)).setReg dst r)
  | .adc => s.cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth 64
    (arithFlags s r (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) (addOverflow a b r)).setReg dst r
  | .sub => let r := a - b
    some ((arithFlags s r (a.toNat < b.toNat) (subOverflow a b r)).setReg dst r)
  | .sbb => s.cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth 64
    (arithFlags s r (a.toNat < b.toNat + c.toNat) (subOverflow a b r)).setReg dst r
  | .cmp => let r := a - b
    some (arithFlags s r (a.toNat < b.toNat) (subOverflow a b r))
  | .and => let r := a &&& b; some ((arithFlags s r false false).setReg dst r)
  | .or => let r := a ||| b; some ((arithFlags s r false false).setReg dst r)
  | .xor => let r := a ^^^ b; some ((arithFlags s r false false).setReg dst r)
  | .test => let r := a &&& b; some (arithFlags s r false false)

def exec : Instr → State → Option State
  | .mov d src, s => (readSrc s src).map fun v => s.setReg d v
  | .store m r, s => s.store64 (s.ea m) (s.gpr r)
  | .alu op d src, s => execAlu op d src s

def addrs : Instr → State → List Addr
  | .mov _ src, s => srcAddrs s src
  | .store m _, s => [s.ea m]
  | .alu _ _ src, s => srcAddrs s src

def eval : Cond → State → Option Bool
  | .e, s => s.zf
  | .ne, s => s.zf.map (!·)
  | .b, s => s.cf
  | .ae, s => s.cf.map (!·)

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval

end VG.X86_64

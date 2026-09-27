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
* Only CF, ZF, SF and OF are modelled. Each is an `Option Bool`; `none` means
  "undefined" (as the SDM specifies for some instructions). Evaluating a
  branch on an undefined flag faults, so verified code never depends on one.
  PF and AF are not modelled, and no modelled instruction reads them.
* Effective addresses are computed modulo 2³² and zero-extended to the 64-bit
  addresses of `Mem` (segment bases are zero: the flat memory model of every
  mainstream 32-bit OS). Memory accesses must lie within the state's permitted
  regions: loads within `rd ++ wr`, stores within `wr`; otherwise the
  instruction faults. Memory is little-endian.
* Instructions whose timing depends on their operands (e.g. `div`) must never
  be added: the constant-time leakage model assumes they do not exist.
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

/-- A memory operand `[base + disp]`. -/
structure MemOp where
  base : Reg
  disp : Nat := 0
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- Branch conditions (`jcc` suffixes). -/
inductive Cond
  /-- `je`: ZF = 1 -/
  | e
  /-- `jne`: ZF = 0 -/
  | ne
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

def exec : Instr → State → Option State
  | .mov d src, s => (readSrc s src).map fun v => s.setReg d v
  | .store m r, s => s.store32 (s.ea m) (s.gpr r)
  | .alu op d src, s => execAlu op d src s
  | .shift op d n, s => execShift op d n s
  | .bswap d, s => some (s.setReg d (bswap (s.gpr d)))

def addrs : Instr → State → List Addr
  | .mov _ src, s => srcAddrs s src
  | .store m _, s => [s.ea m]
  | .alu _ _ src, s => srcAddrs s src
  | .shift .., _ => []
  | .bswap _, _ => []

def eval : Cond → State → Option Bool
  | .e, s => s.zf
  | .ne, s => s.zf.map (!·)

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval

end VG.X86

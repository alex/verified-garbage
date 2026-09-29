import VerifiedGarbage.TCB.Code

/-!
# x86-64 machine state

**Trusted.** The registers, the machine state and memory operands of the
x86-64 model, and the helpers that read and write them. The modelling choices
are described in `TCB/X86_64/Isa.lean`.
-/

namespace VG.X86_64

inductive Reg
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

/-- The SSE registers. -/
inductive XReg
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq, Repr, Inhabited

structure State where
  gpr : Reg → BitVec 64
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  /-- The low 128 bits of each SSE register. -/
  xmm : XReg → BitVec 128 := fun _ => 0
  /-- Bits 255:128 of each AVX register. -/
  ymmHi : XReg → BitVec 128 := fun _ => 0
  /-- The SSE control and status register (SDM Vol. 1 §10.2.3). -/
  mxcsr : BitVec 32 := 0x1F80
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores and, on the ARM targets, what a linker veneer may leave in the
  intra-procedure-call scratch registers (see `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 64 := fun _ => 0

/-- A memory operand `[base + index * scale + disp]`. -/
structure MemOp where
  base : Reg
  index : Option Reg := none
  /-- 1, 2, 4 or 8. -/
  scale : Nat := 1
  disp : Int := 0
  deriving DecidableEq, Repr

/-- The vector length of a VEX-encoded instruction: 128 bits (`xmm`
operands, `VEX.L = 0`) or 256 bits (`ymm` operands, `VEX.L = 1`). -/
inductive VLen | l128 | l256
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

/-- Load 16 bytes, faulting if not permitted. -/
def load128 (s : State) (a : Addr) : Option (BitVec 128) :=
  if InRegions (s.rd ++ s.wr) a 16 then some (s.mem.readW a 128) else none

/-- Store 16 bytes, faulting if not permitted. -/
def store128 (s : State) (a : Addr) (v : BitVec 128) : Option State :=
  if InRegions s.wr a 16 then some { s with mem := s.mem.writeW a v } else none

def setXmm (s : State) (r : XReg) (v : BitVec 128) : State :=
  { s with xmm := fun r' => if r' = r then v else s.xmm r' }

/-- Load 32 bytes, faulting if not permitted. -/
def load256 (s : State) (a : Addr) : Option (BitVec 256) :=
  if InRegions (s.rd ++ s.wr) a 32 then some (s.mem.readW a 256) else none

/-- Store 32 bytes, faulting if not permitted. -/
def store256 (s : State) (a : Addr) (v : BitVec 256) : Option State :=
  if InRegions s.wr a 32 then some { s with mem := s.mem.writeW a v } else none

/-- Lane `i` (bits `128i+127:128i`, for `i` 0 or 1) of an AVX register. -/
def lane (s : State) (r : XReg) (i : Nat) : BitVec 128 := if i = 0 then s.xmm r else s.ymmHi r

/-- The 256 bits of an AVX register. -/
def ymm (s : State) (r : XReg) : BitVec 256 := s.ymmHi r ++ s.xmm r

/-- Write a VEX-encoded instruction's result to `r`: lane 0 is `lo`, and
lane 1 is `hi` for 256-bit operands and 0 for 128-bit ones (SDM Vol. 1
§14.1.3). -/
def setV (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) : State :=
  { s with
    xmm := fun r' => if r' = r then lo else s.xmm r'
    ymmHi := fun r' => if r' = r then (match len with | .l128 => 0 | .l256 => hi) else s.ymmHi r' }

/-- Write a 32-bit result, zero-extended to 64 bits (SDM Vol. 1 §3.4.1.1). -/
def setReg32 (s : State) (r : Reg) (v : BitVec 32) : State := s.setReg r (v.setWidth 64)

/-- Set CF, OF, ZF and SF. -/
def setFlags (s : State) (cf of zf sf : Option Bool) : State :=
  { s with cf := cf, of := of, zf := zf, sf := sf }

end State

end VG.X86_64

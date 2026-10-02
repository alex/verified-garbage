import VerifiedGarbage.TCB.Code

/-!
# IA-32 machine state

**Trusted.** Register, memory and flag definitions of the 32-bit x86 model,
with legacy SSE's eight 128-bit XMM registers (Intel SDM Vol. 1 §10.2.1),
all caller-saved in the System V i386 ABI.
-/

namespace VG.X86

inductive Reg
  | eax | ecx | edx | ebx | esp | ebp | esi | edi
  deriving DecidableEq, Repr, Inhabited

/-- The eight legacy XMM registers available outside 64-bit mode (SDM Vol. 1 §10.2.1). -/
inductive XReg
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  deriving DecidableEq, Repr, Inhabited

structure State where
  gpr : Reg → BitVec 32
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  /-- The 128 bits of each legacy SSE register; no VEX or EVEX instructions are modelled. -/
  xmm : XReg → BitVec 128 := fun _ => 0
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

/-- SDM Vol. 2, MOVDQU: an unaligned 16-byte load, faulting outside readable regions. -/
def load128 (s : State) (a : Addr) : Option (BitVec 128) :=
  if InRegions (s.rd ++ s.wr) a 16 then some (s.mem.readW a 128) else none

/-- SDM Vol. 2, MOVDQU: an unaligned 16-byte store, faulting outside writable regions. -/
def store128 (s : State) (a : Addr) (v : BitVec 128) : Option State :=
  if InRegions s.wr a 16 then some { s with mem := s.mem.writeW a v } else none

def setXmm (s : State) (r : XReg) (v : BitVec 128) : State :=
  { s with xmm := fun r' => if r' = r then v else s.xmm r' }

/-- Set CF, OF, ZF and SF. -/
def setFlags (s : State) (cf of zf sf : Option Bool) : State :=
  { s with cf := cf, of := of, zf := zf, sf := sf }

end State

end VG.X86

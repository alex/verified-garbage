import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.TCB.X86.Isa

/-! # Constant-time RC2 selection on baseline x86

Every candidate is visited in order. Secret indices affect arithmetic masks,
never addresses or branches. The three-register PITABLE lookup leaves the
public key-expansion counters and pointers intact.
-/

namespace VG.Impl.Rc2.X86

open VG.X86

def memOp (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }
def rr (dst src : Reg) : Instr := .mov dst (.reg src)
def imm (dst : Reg) (n : Nat) : Instr := .mov dst (.imm (BitVec.ofNat 32 n))

/-- Equality mask for the low byte in EAX, returned in EDX. -/
def selectMask (i : Nat) : List Instr :=
  [rr .edx .eax, .alu .xor .edx (.imm (BitVec.ofNat 32 i)),
   .alu .sub .edx (.imm 1), .shift .shr .edx 31,
   .alu .xor .edx (.imm 0xffffffff), .alu .add .edx (.imm 1)]

def piStep (i : Nat) : List Instr :=
  selectMask i ++
    ([.alu .and .edx (.imm ((Spec.Rc2.piTable.getD i 0).setWidth 32)),
      .alu .or .ebx (.reg .edx)] : List Instr)

/-- Select PITABLE[EAX & 255]; clobbers EAX, EBX, EDX and flags. -/
def piLookup : List Instr :=
  ([.alu .and .eax (.imm 255), imm .ebx 0] : List Instr) ++
    (List.range 256).flatMap piStep ++ ([rr .eax .ebx] : List Instr)

def loadKey (i : Nat) : List Instr :=
  [.movzx8 .ecx (memOp .edi (2 * i)), .movzx8 .esi (memOp .edi (2 * i + 1)),
   .shift .ror .esi 24, .alu .or .ecx (.reg .esi)]

def keyStep (i : Nat) : List Instr :=
  selectMask i ++ loadKey i ++
    ([.alu .and .ecx (.reg .edx), .alu .or .ebx (.reg .ecx)] : List Instr)

/-- Select schedule[EAX & 63] from EDI; clobbers EAX, EBX, ECX, EDX, ESI and flags. -/
def keyLookup : List Instr :=
  ([.alu .and .eax (.imm 63), imm .ebx 0] : List Instr) ++
    (List.range 64).flatMap keyStep ++ ([rr .eax .ebx] : List Instr)

end VG.Impl.Rc2.X86

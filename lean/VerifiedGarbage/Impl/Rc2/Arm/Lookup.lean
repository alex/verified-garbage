import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.TCB.Arm.Isa

/-! # RC2 selection on ARMv7

Every candidate is visited in a fixed order. Secret indices are used only
in arithmetic masks, never as addresses or branch conditions.
-/

namespace VG.Impl.Rc2.Arm

open VG.Arm

def rr (dst src : Reg) : Instr := .mov dst (.reg src)
def imm (dst : Reg) (n : Nat) : Instr := .movw dst (BitVec.ofNat 16 n)

def mask (r : Reg) (n : Nat) : List Instr :=
  [.mov r (.shifted r .lsl (32 - n)), .mov r (.shifted r .lsr (32 - n))]

def selectMask (i : Nat) : List Instr :=
  [imm .r10 i, .dp .eor .r10 .r12 (.reg .r10), .dp .sub .r10 .r10 (.imm 1),
   .mov .r10 (.shifted .r10 .lsr 31), imm .r11 0, .dp .sub .r11 .r11 (.reg .r10)]

def piStep (i : Nat) : List Instr :=
  selectMask i ++
    ([imm .r10 (Spec.Rc2.piTable.getD i 0).toNat,
      .dp .and .r11 .r11 (.reg .r10), .dp .orr .r3 .r3 (.reg .r11)] : List Instr)

def piLookup : List Instr :=
  mask .r12 8 ++ [imm .r3 0] ++ (List.range 256).flatMap piStep ++ [rr .r12 .r3]

def loadKey (i : Nat) : List Instr :=
  [.ldrb .r8 .r0 (2 * i), .ldrb .r9 .r0 (2 * i + 1),
   .mov .r9 (.shifted .r9 .ror 24), .dp .orr .r8 .r8 (.reg .r9)]

def keyStep (i : Nat) : List Instr :=
  selectMask i ++ loadKey i ++
    ([.dp .and .r8 .r8 (.reg .r11), .dp .orr .r3 .r3 (.reg .r8)] : List Instr)

def keyLookup : List Instr :=
  mask .r12 6 ++ [imm .r3 0] ++ (List.range 64).flatMap keyStep ++ [rr .r12 .r3]

end VG.Impl.Rc2.Arm

import VerifiedGarbage.Impl.Ed25519.Arm.Field

/-! Canonical reduction in the multiplication accumulator. The working
field elements are preserved; the two temporary fields occupy [1472,1600). -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def FR : Nat := ACC
def FY : Nat := ACC + 64

def freezeCopy (a : Slot) : List Instr :=
  (List.range 16).flatMap fun k =>
    [.ldr .r3 .r0 (offset a + 4 * k), .str .r3 .r0 (FR + 4 * k)]

def low15 : List Instr := [.mov .r3 (.shifted .r3 .lsl 17), .mov .r3 (.shifted .r3 .lsr 17)]

def freezeA : List Instr :=
  [.movw .r6 0xffff, .ldr .r3 .r0 (FR + 60), .mov .r5 (.shifted .r3 .lsr 15)] ++ low15 ++
  [.str .r3 .r0 (FR + 60), .mov .r2 (.imm 19), .mul .r5 .r5 .r2]

def freezeB : List Instr :=
  [.ldr .r3 .r0 (FY + 60), .mov .r9 (.shifted .r3 .lsr 15), .mov .r1 (.imm 0),
    .dp .sub .r9 .r1 (.reg .r9)] ++ low15 ++ [.str .r3 .r0 (FY + 60)]

def selectSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (FR + 4 * k), .ldr .r2 .r0 (FY + 4 * k), .dp .eor .r2 .r2 (.reg .r3),
    .dp .and .r2 .r2 (.reg .r9), .dp .eor .r3 .r3 (.reg .r2)]

def freezeSelect : List Instr :=
  (List.range 16).flatMap fun k => selectSrc k ++ [.str .r3 .r0 (FR + 4 * k)]

def freezeCore : List Instr :=
  freezeA ++ pass .r0 FR (ldSrc FR) ++ [.mov .r5 (.imm 19)] ++
    pass .r0 FY (ldSrc FR) ++ freezeB ++ freezeSelect

def freeze (a : Slot) : List Instr := freezeCopy a ++ freezeCore

end VG.Impl.Ed25519.Arm

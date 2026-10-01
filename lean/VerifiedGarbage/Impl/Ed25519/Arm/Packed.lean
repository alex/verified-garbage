import VerifiedGarbage.Impl.Ed25519.Arm.Field

/-! Pack each sixteen-bit limb into two bytes. Tables use 128 bytes per
extended point; arithmetic continues to use 256 bytes per point. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def packStep (a dst k : Nat) : List Instr :=
  [.ldr .r3 .r0 (a + 4 * k), .strb .r3 .r12 (dst + 2 * k),
    .mov .r3 (.shifted .r3 .lsr 8), .strb .r3 .r12 (dst + 2 * k + 1)]

def packField (a dst : Nat) : List Instr := (List.range 16).flatMap (packStep a dst)

def unpackSrc (src k : Nat) : List Instr :=
  [.ldrb .r3 .r12 (src + 2 * k), .ldrb .r2 .r12 (src + 2 * k + 1),
    .dp .add .r3 .r3 (.shifted .r2 .lsl 8)]

def unpackField (o src : Nat) : List Instr :=
  (List.range 16).flatMap fun k => unpackSrc src k ++ [.str .r3 .r0 (o + 4 * k)]

def pointToTable : List Instr :=
  (List.range 4).flatMap fun j => packField (64 + 64 * j) (32 * j)

def pointFromTable : List Instr :=
  (List.range 4).flatMap fun j => unpackField (64 + 64 * j) (32 * j)

end VG.Impl.Ed25519.Arm

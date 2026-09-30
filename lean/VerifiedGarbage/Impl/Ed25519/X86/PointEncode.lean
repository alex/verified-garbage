import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory
import VerifiedGarbage.Impl.Ed25519.X86.Power

/-! Canonical Edwards encoding is left in the eight words of slot1. -/
namespace VG.Impl.Ed25519.X86
open VG.X86
open VG.Impl.X25519.X86 (sc freeze)

def affineOps : List FieldOp := [.mul 0 0 15, .mul 1 1 15]
def pointAffine : Prog isa := .seq invert (.block (fieldCode affineOps))
def pointSign : List Instr :=
  [.mov .esi (.mem (sc 64)), .alu .and .esi (.imm 1), .shift .ror .esi 1]
def encodeSign : List Instr :=
  [.mov .eax (.mem (sc 124)), .alu .add .eax (.reg .esi), .store (sc 124) .eax]
def pointEncode : Prog isa :=
  .seq pointAffine (.block (freeze 64 ++ pointSign ++ freeze 96 ++ encodeSign))

end VG.Impl.Ed25519.X86

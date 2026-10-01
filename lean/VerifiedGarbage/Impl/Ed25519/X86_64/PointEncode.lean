import VerifiedGarbage.Impl.Ed25519.X86_64.FieldMemory

/-! Encode the current extended point, leaving four output words in r8-r11. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def affineOps : List FieldOp := [.mul 0 0 15, .mul 1 1 15]

def pointAffine (fld : Arith) : Prog isa :=
  .seq (VG.Impl.X25519.X86_64.invert fld) (.block (fieldCode fld affineOps))

def pointSign : List Instr :=
  [.mov .rbx (.reg .r8), .alu .and .rbx (.imm 1), .shift .ror .rbx 1]

def pointEncode (fld : Arith) : Prog isa :=
  .seq (pointAffine fld) (.block (VG.Impl.X25519.X86_64.freeze 64 ++ pointSign ++
    VG.Impl.X25519.X86_64.freeze 96 ++ [.alu .add .r11 (.reg .rbx)]))

end VG.Impl.Ed25519.X86_64

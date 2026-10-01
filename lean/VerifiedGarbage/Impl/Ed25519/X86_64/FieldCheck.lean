import VerifiedGarbage.Impl.Ed25519.X86_64.Field

/-! Equality tests used only on the public inputs of signature verification. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- ZF is set precisely when the four canonical words are zero. -/
def wordsZero : List Instr :=
  [.mov .rax (.reg .r8), .alu .or .rax (.reg .r9), .alu .or .rax (.reg .r10),
    .alu .or .rax (.reg .r11), .alu .test .rax (.reg .rax)]

def fieldZero (a : Slot) : List Instr := VG.Impl.X25519.X86_64.freeze (offset a) ++ wordsZero

/-- Slot 21 is temporary. -/
def fieldEqual (fld : Arith) (a b : Slot) : List Instr := fieldCode fld [.sub 21 a b] ++ fieldZero 21

end VG.Impl.Ed25519.X86_64

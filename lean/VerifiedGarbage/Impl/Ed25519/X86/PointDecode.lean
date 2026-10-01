import VerifiedGarbage.Impl.Ed25519.X86.RecoverSign

namespace VG.Impl.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

/-- The encoding has been copied into slot 1. Save its sign at byte 32. -/
def decodeY : List Instr :=
  [.mov .esi (.mem (sc 124)), .shift .shr .esi 31, .store (sc 32) .esi,
    .mov .eax (.mem (sc 124)), .alu .and .eax (.imm low31), .store (sc 124) .eax]

def canonicalY : List Instr :=
  [.mov .ebx (.imm 19), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] ++
    cols T 8 (fun k => [.addM (96 + 4 * k)]) ++
      [.mov .eax (.mem (sc (T + 28))), .shift .shr .eax 31, .alu .test .eax (.reg .eax)]

def pointDecode : Prog isa :=
  .seq (.block (decodeY ++ canonicalY)) (.ite .e recoverPoint recoverInvalid)

end VG.Impl.Ed25519.X86

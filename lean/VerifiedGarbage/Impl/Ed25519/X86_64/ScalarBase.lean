import VerifiedGarbage.Impl.Ed25519.X86_64.Scalar
import VerifiedGarbage.Impl.Ed25519.X86_64.Bits
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Impl.Ed25519.X86_64.PointEncode

/-! Base-point multiplication for the complete unsigned 256-bit input scalar. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ sc)

def scalarBaseInit : List Instr := constField 16 Spec.Ed25519.d ++ constPoint Spec.Ed25519.basePoint

def scalarBasePrepare : Prog isa :=
  .seq (scalarBits 32) (.block scalarBaseInit)

def scalarBaseEngine : Prog isa :=
  .seq scalarBasePrepare (.seq (pointMultiply 16) pointEncode)

def scalarBaseSetup : List Instr :=
  [.store (at_ .rdx 48) .rdi, .mov .rdi (.reg .rdx)]

def scalarBaseFinishArgs : List Instr := [.mov .rdx (.reg .rdi), .mov .rdi (.mem (sc 48))]

def scalarBaseFinish : Prog isa :=
  .seq (.block scalarBaseFinishArgs) (.block (scalarRestore ++
    [.store (at_ .rdi 0) .r8, .store (at_ .rdi 8) .r9,
      .store (at_ .rdi 16) .r10, .store (at_ .rdi 24) .r11]))

def scalarBaseWith (engine : Prog isa) : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq engine scalarBaseFinish)

def scalarBase : Prog isa := scalarBaseWith scalarBaseEngine

end VG.Impl.Ed25519.X86_64

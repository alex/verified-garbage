import VerifiedGarbage.Impl.Ed25519.X86_64.Recover

/-! Check negative zero and select the decoded x-coordinate's public sign. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- The public sign bit is 0 or 1 in rsi. -/
def recoverParity : List Instr :=
  [.mov .rax (.reg .r8), .alu .and .rax (.imm 1), .alu .xor .rax (.reg .rsi),
    .alu .test .rax (.reg .rax)]

def recoverSuccessOps : List FieldOp := [.const 2 1, .mul 3 0 1]

def recoverSuccess (fld : Arith) : List Instr := fieldCode fld recoverSuccessOps ++ [.mov32 .rax (.imm 1)]

def recoverAdjustSign (fld : Arith) : Prog isa :=
  .seq (.block (VG.Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity))
    (.seq (.ite .e (.block []) (.block (fieldCode fld [.const 5 0, .sub 0 5 0])))
      (.block (recoverSuccess fld)))

def recoverInvalid : Prog isa := .block [.mov32 .rax (.imm 0)]

def recoverSign (fld : Arith) : Prog isa :=
  .seq (.block (fieldZero 0)) (.ite .e
    (.seq (.block [.alu .test .rsi (.reg .rsi)]) (.ite .ne recoverInvalid (recoverAdjustSign fld)))
    (recoverAdjustSign fld))

/-- The sign bit is in rsi; the canonical y-coordinate is in slot 1. -/
def recoverPoint (fld : Arith) : Prog isa :=
  .seq (recoverCandidate fld) (.seq (.block (fieldEqual fld 11 6)) (.ite .e (recoverSign fld)
    (.seq (.block (fieldEqual fld 11 12)) (.ite .e
      (.seq (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (recoverSign fld))
      recoverInvalid))))

end VG.Impl.Ed25519.X86_64

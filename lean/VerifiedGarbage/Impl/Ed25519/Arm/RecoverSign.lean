import VerifiedGarbage.Impl.Ed25519.Arm.Recover

/-! Validate the candidate and choose the public encoded sign, saved at offset 60. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def recoverParity : List Instr :=
  [.ldr .r3 .r0 FR, .dp .and .r9 .r3 (.imm 1), .ldr .r2 .r0 60,
    .dp .eor .r9 .r9 (.reg .r2), .cmp .r9 (.imm 0)]

def recoverSuccessOps : List FieldOp := [.const 2 1, .mul 3 0 1]
def recoverSuccess : Prog isa := .seq (fieldCode recoverSuccessOps) (.block [.mov .r9 (.imm 1)])
def recoverInvalid : Prog isa := .block [.mov .r9 (.imm 0)]

def recoverAdjustSign : Prog isa :=
  .seq (.block (freeze 0 ++ recoverParity))
    (.seq (.ite .eq (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) recoverSuccess)

def signTest : List Instr := [.ldr .r3 .r0 60, .cmp .r3 (.imm 0)]

def recoverSign : Prog isa :=
  .seq (fieldZero 0) (.ite .eq
    (.seq (.block signTest) (.ite .ne recoverInvalid recoverAdjustSign)) recoverAdjustSign)

def recoverPoint : Prog isa :=
  .seq recoverCandidate (.seq (fieldEqual 11 6) (.ite .eq recoverSign
    (.seq (fieldEqual 11 12) (.ite .eq
      (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) recoverSign)
      recoverInvalid))))

end VG.Impl.Ed25519.Arm

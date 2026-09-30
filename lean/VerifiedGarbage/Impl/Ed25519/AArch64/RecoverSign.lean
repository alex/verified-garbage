import VerifiedGarbage.Impl.Ed25519.AArch64.Recover

/-! Check negative zero and choose the public sign of a decoded point. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def recoverParity : List Instr :=
  [.movz .w .x9 1 0, .logic .and .x .x8 .x4 .x9, .logic .eor .x .x8 .x8 .x1]

def recoverSuccessOps : List FieldOp := [.const 2 1, .mul 3 0 1]
def recoverSuccess : List Instr := fieldCode recoverSuccessOps ++ [.movz .w .x8 1 0]

def recoverAdjustSign : Prog isa :=
  .seq (.block (freeze (offset 0) ++ recoverParity))
    (.seq (.ite (.zero .x .x8) (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
      (.block recoverSuccess))

def recoverInvalid : Prog isa := .block [.movz .w .x8 0 0]

def recoverSign : Prog isa :=
  .seq (.block (fieldZero 0)) (.ite (.zero .x .x8)
    (.ite (.nonzero .x .x1) recoverInvalid recoverAdjustSign) recoverAdjustSign)

def recoverPoint : Prog isa :=
  .seq recoverCandidate (.seq (.block (fieldEqual 11 6)) (.ite (.zero .x .x8) recoverSign
    (.seq (.block (fieldEqual 11 12)) (.ite (.zero .x .x8)
      (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign)
      recoverInvalid))))

end VG.Impl.Ed25519.AArch64

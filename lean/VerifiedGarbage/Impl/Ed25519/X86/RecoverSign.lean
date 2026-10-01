import VerifiedGarbage.Impl.Ed25519.X86.Recover

namespace VG.Impl.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def recoverParity : List Instr :=
  [.mov .eax (.mem (sc 64)), .alu .and .eax (.imm 1), .alu .xor .eax (.reg .esi),
    .alu .test .eax (.reg .eax)]

def recoverSuccessOps : List FieldOp := [.const 2 1, .mul 3 0 1]
def recoverSuccess : List Instr := fieldCode recoverSuccessOps ++ [.mov .eax (.imm 1)]
def recoverInvalid : Prog isa := .block [.mov .eax (.imm 0)]
def recoverAdjustSign : Prog isa :=
  .seq (.block (freeze 64 ++ recoverParity))
    (.seq (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) (.block recoverSuccess))
def recoverSign : Prog isa :=
  .seq (.block (fieldZero 0)) (.ite .e
    (.seq (.block [.alu .test .esi (.reg .esi)]) (.ite .ne recoverInvalid recoverAdjustSign)) recoverAdjustSign)
def recoverChecks : Prog isa :=
  .seq (.block (fieldEqual 11 6)) (.ite .e recoverSign
    (.seq (.block (fieldEqual 11 12)) (.ite .e
      (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid)))
def recoverPoint : Prog isa :=
  .seq recoverCandidate (.seq (.block [.mov .esi (.mem (sc 32))]) recoverChecks)

end VG.Impl.Ed25519.X86

import VerifiedGarbage.Impl.Ed25519.X86_64.RootPower
import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck

/-! Recover a candidate x-coordinate from y, before checking its square and sign. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- y is in slot 1. Prepare u, v, v^3, and the root exponentiation input. -/
def recoverInitOps : List FieldOp := [
  .const 16 Spec.Ed25519.d, .const 4 1, .sqr 5 1, .sub 6 5 4,
  .mul 7 16 1, .mul 7 7 1, .add 7 7 4,
  .sqr 8 7, .mul 9 8 7, .sqr 10 9, .mul 10 10 7, .mul 2 6 10]

def recoverFinishOps : List FieldOp := [
  .const 5 0, .sub 12 5 6, .mul 0 6 9, .mul 0 0 15, .mul 11 7 0, .mul 11 11 0]

def recoverCandidate (fld : Arith) : Prog isa :=
  .seq (.block (fieldCode fld recoverInitOps)) (.seq (rootPower fld) (.block (fieldCode fld recoverFinishOps)))

end VG.Impl.Ed25519.X86_64

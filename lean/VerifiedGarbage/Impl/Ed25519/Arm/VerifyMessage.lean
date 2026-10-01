import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
import VerifiedGarbage.Impl.Ed25519.Arm.Verify
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Impl.Sha512.Arm.Stream
import VerifiedGarbage.Spec.Sha512.Contract

namespace VG.Impl.Ed25519.Arm.VerifyMessage
open VG.Arm VG.Impl.Ed25519.Arm.Whole

def initArgs : List Instr := setup [(.r0,.caller 4 0)] []
def prefixArgs (source count : Nat) : List Instr :=
  setup [(.r0,.caller 4 0),(.r2,.const count),(.r3,.const 0)]
    [.caller source 0,.const 32,.caller 4 192]
def messageArgs (count : Nat) : List Instr :=
  setup [(.r0,.caller 4 0),(.r2,.const count),(.r3,.const 0)]
    [.caller 1 0,.caller 2 0,.caller 4 192]
def finalizeArgs (n : Nat) (b : Bool) : List Instr :=
  setup [(.r0,.caller 4 0),(.r2,if b then .caller 2 n else .const n),(.r3,.const 0)]
    [.frame 184,.caller 4 192]
def init : Prog isa := callWith initArgs Spec.Sha512.init512Api.name
  (Sha512.Arm.Stream.init Spec.Sha512.H0_512)
def update (args : List Instr) : Prog isa :=
  callWith args Spec.Sha512.updateApi.name Sha512.Arm.Stream.update
def finalize (n : Nat) (b : Bool) : Prog isa :=
  callWith (finalizeArgs n b) Spec.Sha512.finalizeApi.name Sha512.Arm.Stream.finalize
def hash : Prog isa :=
  .seq init (.seq (update (prefixArgs 3 0))
    (.seq (update (prefixArgs 0 32)) (.seq (update (messageArgs 64)) (finalize 64 true))))
def reduceArgs : List Instr :=
  setup [(.r0,.frame 120),(.r1,.frame 184),(.r2,.caller 4 0)] []
def extendChallenge : List Instr := zeroWords 38 8
def equationArgs : List Instr :=
  setup [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)] []
def body : Prog isa :=
  .seq hash (.seq (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce)
    (.seq (.block extendChallenge) (callWith equationArgs "vg_ed25519_verify_equation" verifyEquation)))
def code : Prog isa := wrap 5 body

end VG.Impl.Ed25519.Arm.VerifyMessage

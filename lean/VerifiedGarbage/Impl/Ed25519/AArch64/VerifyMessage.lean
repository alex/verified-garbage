import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Impl.Sha512.AArch64.Stream
import VerifiedGarbage.Spec.Sha512.Contract

/-! Whole-message verification with every SHA-512 backend. -/
namespace VG.Impl.Ed25519.AArch64.VerifyMessage
open VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def initArgs : List Instr := setup [(.x0, .caller 4 0)]
def prefixArgs (source count : Nat) : List Instr :=
  setup [(.x0, .caller 4 0), (.x1, .const count), (.x2, .caller source 0),
    (.x3, .const 32), (.x4, .caller 4 192)]
def messageArgs : List Instr :=
  setup [(.x0, .caller 4 0), (.x1, .const 64), (.x2, .caller 1 0),
    (.x3, .caller 2 0), (.x4, .caller 4 192)]
def finalizeArgs : List Instr :=
  setup [(.x0, .caller 4 0), (.x1, .caller 2 64), (.x2, .frame 192), (.x3, .caller 4 192)]

def init : Prog isa := callWith initArgs Spec.Sha512.init512Api.name
  (Sha512.AArch64.Stream.init Spec.Sha512.H0_512)
def update (compress : Prog isa) (suffix : String) (args : List Instr) : Prog isa :=
  callWith args (Spec.Sha512.updateApi.name ++ suffix) (Sha512.AArch64.Stream.updateWith compress)
def finalize (compress : Prog isa) (suffix : String) : Prog isa :=
  callWith finalizeArgs (Spec.Sha512.finalizeApi.name ++ suffix) (Sha512.AArch64.Stream.finalizeWith compress)
def hash (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq init (.seq (update compress suffix (prefixArgs 3 0))
    (.seq (update compress suffix (prefixArgs 0 32))
      (.seq (update compress suffix messageArgs) (finalize compress suffix))))
def reduceArgs : List Instr :=
  setup [(.x0, .frame 128), (.x1, .frame 192), (.x2, .caller 4 0)]
def extendChallenge : List Instr := zeroWords 20 4
def equationArgs : List Instr :=
  setup [(.x0, .caller 0 0), (.x1, .caller 3 0), (.x2, .frame 128), (.x3, .caller 4 0)]
def body (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq (hash compress suffix)
    (.seq (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce)
      (.seq (.block extendChallenge)
        (callWith equationArgs "vg_ed25519_verify_equation" verifyEquation)))
def code (compress : Prog isa) (suffix : String) : Prog isa := wrap (body compress suffix)

end VG.Impl.Ed25519.AArch64.VerifyMessage

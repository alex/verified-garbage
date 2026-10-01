import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
import VerifiedGarbage.Impl.Ed25519.X86.Scalar
import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Impl.Ed25519.X86.Whole.Wipe

/-! Complete x86 Ed25519 verification: hash R || A || message, reduce the
challenge modulo L, and invoke the verified strict equation checker. -/
namespace VG.Impl.Ed25519.X86.VerifyMessage
open VG.X86
open VG.Impl.Ed25519.X86.PublicKey (at_ argument callWith)

open VG.Impl.Ed25519.X86.Whole (setup)

def initArgs : List Instr := setup 0 [.caller 4 0]

def prefixArgs (source count : Nat) : List Instr :=
  setup 0 [.caller 4 0, .const count, .const 0, .caller source 0, .const 32, .caller 4 192]

def messageArgs : List Instr :=
  setup 0 [.caller 4 0, .const 64, .const 0, .caller 1 0, .caller 2 0, .caller 4 192]

def finalizeArgs : List Instr :=
  setup 0 [.caller 4 0, .const 0, .const 0, .frame 192, .caller 4 192] ++
    Whole.countArgs 2 64

def init : Prog isa :=
  callWith initArgs Spec.Sha512.init512Api.name (Sha512.X86.Stream.init Spec.Sha512.H0_512)

def update (args : List Instr) : Prog isa :=
  callWith args Spec.Sha512.updateApi.name Sha512.X86.Stream.update

def hash : Prog isa :=
  .seq (callWith initArgs Spec.Sha512.init512Api.name (Sha512.X86.Stream.init Spec.Sha512.H0_512))
  (.seq (callWith (prefixArgs 3 0) Spec.Sha512.updateApi.name Sha512.X86.Stream.update)
  (.seq (callWith (prefixArgs 0 32) Spec.Sha512.updateApi.name Sha512.X86.Stream.update)
  (.seq (callWith messageArgs Spec.Sha512.updateApi.name Sha512.X86.Stream.update)
    (callWith finalizeArgs Spec.Sha512.finalizeApi.name Sha512.X86.Stream.finalize))))

def reduceArgs : List Instr := setup 0 [.frame 128, .frame 192, .caller 4 0]

def extendChallenge : List Instr := Whole.zeroWords 40 8

def equationArgs : List Instr := setup 0 [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0]

def body : Prog isa := .seq hash
  (.seq (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce)
  (.seq (.block extendChallenge) (callWith equationArgs "vg_ed25519_verify_equation" verifyEquation)))

def code : Prog isa :=
  .frame (.push (List.replicate 64 .eax)) body (.pop .edx 64)

end VG.Impl.Ed25519.X86.VerifyMessage

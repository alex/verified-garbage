import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
import VerifiedGarbage.Impl.Sha512.Arm.Stream
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Impl.Ed25519.Arm.SignCached.Prefix
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarMulAdd
import VerifiedGarbage.Spec.Ed25519.CachedSign

/-! Complete ARMv7 cached-key signing, including SHA-512. The 248-byte
local frame contains scalar24, prefix56, nonce88, challenge120 and digest184.
Saved caller arguments begin at248. All secret locals are cleared. -/
namespace VG.Impl.Ed25519.Arm.SignCached
open VG.Arm VG.Impl.Ed25519.Arm.Whole

def initArgs : List Instr := setup [(.r0, .caller 5 0)] []
def inputArgs (source count : Nat) : List Instr :=
  setup [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)]
    [.caller source 0, .const 32, .caller 5 192]
def prefixArgs : List Instr :=
  setup [(.r0, .caller 5 0), (.r2, .const 0), (.r3, .const 0)]
    [.frame 56, .const 32, .caller 5 192]
def messageArgs (count : Nat) : List Instr :=
  setup [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)]
    [.caller 3 0, .caller 4 0, .caller 5 192]
def finalizeArgs (prefixLen : Nat) (withMessage : Bool) : List Instr :=
  setup [(.r0, .caller 5 0), (.r2, if withMessage then .caller 4 prefixLen else .const prefixLen),
    (.r3, .const 0)] [.frame 184, .caller 5 192]

def init : Prog isa := callWith initArgs Spec.Sha512.init512Api.name
  (Sha512.Arm.Stream.init Spec.Sha512.H0_512)
def update (args : List Instr) : Prog isa :=
  callWith args Spec.Sha512.updateApi.name Sha512.Arm.Stream.update
def finalize (n : Nat) (b : Bool) : Prog isa :=
  callWith (finalizeArgs n b) Spec.Sha512.finalizeApi.name Sha512.Arm.Stream.finalize

def hashSeed : Prog isa := .seq init (.seq (update (inputArgs 1 0)) (finalize 32 false))
def saveSecret : List Instr := PublicKey.prune ++ copyPrefix

def hashNonce : Prog isa := .seq init (.seq (update prefixArgs)
  (.seq (update (messageArgs 32)) (finalize 32 true)))
def reduceArgs (out : Nat) : List Instr :=
  setup [(.r0, .frame out), (.r1, .frame 184), (.r2, .caller 5 0)] []
def reduce (out : Nat) : Prog isa := callWith (reduceArgs out) "vg_ed25519_scalar_reduce" scalarReduce

def baseArgs : List Instr := setup [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] []
def hashChallenge : Prog isa := .seq init (.seq (update (inputArgs 0 0))
  (.seq (update (inputArgs 2 32)) (.seq (update (messageArgs 64)) (finalize 64 true))))
def mulAddArgs : List Instr :=
  setup [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120), (.r3, .frame 24)] [.caller 5 0]
def wipe : List Instr := zeroWords 6 56

def secretCode : Prog isa := .seq hashSeed (.block saveSecret)
def nonceCode : Prog isa := .seq hashNonce (.seq (reduce 88)
  (callWith baseArgs "vg_ed25519_scalar_base" scalarBase))
def challengeCode : Prog isa := .seq hashChallenge (.seq (reduce 120)
  (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd))
def body : Prog isa := .seq secretCode (.seq nonceCode (.seq challengeCode (.block wipe)))
def code : Prog isa := wrap 6 body

end VG.Impl.Ed25519.Arm.SignCached

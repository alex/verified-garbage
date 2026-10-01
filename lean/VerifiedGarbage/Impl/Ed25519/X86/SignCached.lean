import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
import VerifiedGarbage.Impl.Ed25519.X86.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Impl.Ed25519.X86.Scalar
import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
import VerifiedGarbage.Spec.Ed25519.CachedSign

/-! Complete cached-key Ed25519 signing on x86. The 256-byte frame holds
outgoing cdecl arguments at 0..24, scalar at 32, prefix at 64, nonce at 96,
challenge at 128 and digest at 192. Original caller arguments remain above
the frame. Hashing uses scratch[0..192) for state and scratch[192..464) for
working memory. Primitive calls may overwrite the entire scratch buffer.
The 64-bit finalization count includes carry from the 32-bit message length.
All secret frame buffers are cleared before returning. -/
namespace VG.Impl.Ed25519.X86.SignCached
open VG.X86
open PublicKey (at_ argument callWith)

def initArgs : List Instr := Whole.setup 0 [.caller 5 0]

def inputArgs (source count : Nat) : List Instr :=
  Whole.setup 0 [.caller 5 0, .const count, .const 0, .caller source 0, .const 32, .caller 5 192]

def prefixArgs : List Instr :=
  Whole.setup 0 [.caller 5 0, .const 0, .const 0, .frame 64, .const 32, .caller 5 192]

def messageArgs (count : Nat) : List Instr :=
  Whole.setup 0 [.caller 5 0, .const count, .const 0, .caller 3 0, .caller 4 0, .caller 5 192]


def finalizeArgs (prefixLen : Nat) (withMessage : Bool) : List Instr :=
  Whole.setup 0 [.caller 5 0, .const prefixLen, .const 0, .frame 192, .caller 5 192] ++
    if withMessage then Whole.countArgs 4 prefixLen else []

def init : Prog isa := callWith initArgs Spec.Sha512.init512Api.name
  (Sha512.X86.Stream.init Spec.Sha512.H0_512)

def update (args : List Instr) : Prog isa :=
  callWith args Spec.Sha512.updateApi.name Sha512.X86.Stream.update

def finalize (prefixLen : Nat) (withMessage : Bool) : Prog isa :=
  callWith (finalizeArgs prefixLen withMessage) Spec.Sha512.finalizeApi.name Sha512.X86.Stream.finalize

def hashSeed : Prog isa :=
  .seq init (.seq (update (inputArgs 1 0)) (finalize 32 false))

def copyWord (source destination k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ (source + 4 * k))), .store (at_ (destination + 4 * k)) .eax]

def copyPrefix : List Instr := (List.range 8).flatMap (copyWord 224 64)

def saveSecret : List Instr := PublicKey.prune ++ copyPrefix

def hashNonce : Prog isa :=
  .seq init (.seq (update prefixArgs) (.seq (update (messageArgs 32)) (finalize 32 true)))

def reduceArgs (out : Nat) : List Instr :=
  Whole.setup 0 [.frame out, .frame 192, .caller 5 0]

def reduce (out : Nat) : Prog isa :=
  callWith (reduceArgs out) "vg_ed25519_scalar_reduce" scalarReduce

def baseArgs : List Instr :=
  Whole.setup 0 [.caller 0 0, .frame 96, .caller 5 0]

def hashChallenge : Prog isa :=
  .seq init (.seq (update (inputArgs 0 0)) (.seq (update (inputArgs 2 32))
    (.seq (update (messageArgs 64)) (finalize 64 true))))

def mulAddArgs : List Instr :=
  Whole.setup 0 [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]

def wipe : List Instr := Whole.zeroWords 8 56

def secretCode : Prog isa := .seq hashSeed (.block saveSecret)
def nonceCode : Prog isa := .seq hashNonce (.seq (reduce 96)
  (callWith baseArgs "vg_ed25519_scalar_base" scalarBase))
def challengeCode : Prog isa := .seq hashChallenge (.seq (reduce 128)
  (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd))
def body : Prog isa := .seq secretCode (.seq nonceCode (.seq challengeCode (.block wipe)))

def code : Prog isa :=
  .frame (.push (List.replicate 64 .eax)) body (.pop .eax 64)

end VG.Impl.Ed25519.X86.SignCached

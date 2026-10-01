import VerifiedGarbage.Impl.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Impl.Ed25519.X86.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Spec.Sha512.Contract

/-! Ed25519 public-key derivation, including SHA-512 and pruning, on x86.
The 256-byte frame holds outgoing cdecl arguments at 0, the scalar at 32,
and the digest at 192. The original arguments remain above the frame.
SHA-512's state and working space use the caller's scratch buffer. -/
namespace VG.Impl.Ed25519.X86.PublicKey
open VG.X86

def at_ (d : Nat) : MemOp := { base := .esp, disp := d }

def argument (j : Nat) : MemOp := at_ (260 + 4 * j)

def initArgs : List Instr := Whole.setup 0 [.caller 2 0]

def updateArgs : List Instr :=
  Whole.setup 0 [.caller 2 0, .const 0, .const 0, .caller 1 0, .const 32, .caller 2 192]

def finalizeArgs : List Instr :=
  Whole.setup 0 [.caller 2 0, .const 32, .const 0, .frame 192, .caller 2 192]

def baseArgs : List Instr := Whole.setup 0 [.caller 0 0, .frame 32, .caller 2 0]

/-- Prune one word; the other words are copied unchanged. -/
def pruneWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ (192 + 4 * k)))] ++
  (if k = 0 then [.alu .and .eax (.imm 0xfffffff8)] else []) ++
  (if k = 7 then [.alu .and .eax (.imm 0x3fffffff), .alu .or .eax (.imm 0x40000000)] else []) ++
  [.store (at_ (32 + 4 * k)) .eax]

def prune : List Instr := (List.range 8).flatMap pruneWord

def wipe : List Instr := Whole.zeroWords 8 56

def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

def hash : Prog isa :=
  .seq (callWith initArgs Spec.Sha512.init512Api.name (Sha512.X86.Stream.init Spec.Sha512.H0_512))
  (.seq (callWith updateArgs Spec.Sha512.updateApi.name Sha512.X86.Stream.update)
    (callWith finalizeArgs Spec.Sha512.finalizeApi.name Sha512.X86.Stream.finalize))

def body : Prog isa := .seq hash (.seq (.block prune)
  (.seq (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) (.block wipe)))

def publicKey : Prog isa :=
  .frame (.push (List.replicate 64 .eax)) body (.pop .eax 64)

end VG.Impl.Ed25519.X86.PublicKey

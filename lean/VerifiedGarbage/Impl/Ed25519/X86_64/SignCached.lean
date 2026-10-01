import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey
import VerifiedGarbage.Impl.Ed25519.X86_64.Scalar
import VerifiedGarbage.Impl.Ed25519.X86_64.MulAdd

/-!
# Complete Ed25519 signing with the matching cached public key

All three SHA-512 computations, pruning, nonce reduction, base-point
multiplication and scalar multiply-add execute inside this operation.
The caller supplies the key derived from the seed, as required by the
reviewed `signCachedContract`.

The 248-byte frame holds the scalar (0), nonce prefix (32), nonce (64),
challenge (96), hash digest (128), an unused alignment word (192), and six
saved arguments (200..248). SHA-512's state and working space are in
scratch. Every scalar and hash input to an Ed25519 primitive is outside
scratch, which those primitives overwrite. Secret frame buffers are wiped
before returning. Calls need another 16 bytes below the frame.
-/
namespace VG.Impl.Ed25519.X86_64.SignCached
open VG.X86_64
open VG.Impl.Sha512.X86_64.Stream (Callee)

def fScratch : Nat := 200
def fLength : Nat := 208
def fMessage : Nat := 216
def fPublicKey : Nat := 224
def fSeed : Nat := 232
def fOut : Nat := 240

def framePtr (r : Reg) (offset : Nat) : List Instr :=
  [.mov r (.reg .rsp), .alu .add r (.imm (BitVec.ofNat 32 offset))]

def scrPtr (r : Reg) (offset : Nat) : List Instr :=
  [.mov r (.mem (stk fScratch)), .alu .add r (.imm (BitVec.ofNat 32 offset))]

def initArgs : List Instr := [.mov .rdi (.mem (stk fScratch))]

def inputArgs (source count : Nat) : List Instr :=
  ([.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm (BitVec.ofNat 32 count)),
    .mov .rdx (.mem (stk source)), .mov32 .rcx (.imm 32)] : List Instr) ++ scrPtr .r8 shaScratch

def prefixArgs : List Instr :=
  ([.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm 0)] : List Instr) ++
    framePtr .rdx 32 ++ ([.mov32 .rcx (.imm 32)] : List Instr) ++ scrPtr .r8 shaScratch

def messageArgs (count : Nat) : List Instr :=
  ([.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm (BitVec.ofNat 32 count)),
    .mov .rdx (.mem (stk fMessage)), .mov .rcx (.mem (stk fLength))] : List Instr) ++ scrPtr .r8 shaScratch

def finalizeArgs (prefixLen : Nat) (withMessage : Bool) : List Instr :=
  ([.mov .rdi (.mem (stk fScratch))] : List Instr) ++
    (if withMessage then [.mov .rsi (.mem (stk fLength)), .alu .add .rsi (.imm (BitVec.ofNat 32 prefixLen))]
     else [.mov32 .rsi (.imm (BitVec.ofNat 32 prefixLen))]) ++
    framePtr .rdx 128 ++ scrPtr .rcx shaScratch

def init : Prog isa := callWith initArgs Spec.Sha512.init512Api.name
  (Sha512.X86_64.Stream.init Spec.Sha512.H0_512)

def update (f : Callee) (suffix : String) (args : List Instr) : Prog isa :=
  callWith args (Spec.Sha512.updateApi.name ++ suffix) (Sha512.X86_64.Stream.update f)

def finalize (f : Callee) (suffix : String) (prefixLen : Nat) (withMessage : Bool) : Prog isa :=
  callWith (finalizeArgs prefixLen withMessage) (Spec.Sha512.finalizeApi.name ++ suffix)
    (Sha512.X86_64.Stream.finalize f)

def hashSeed (f : Callee) (suffix : String) : Prog isa :=
  .seq init (.seq (update f suffix (inputArgs fSeed 0)) (finalize f suffix 32 false))

def pruneRegs : List Instr :=
  [.mov .r8 (.mem (stk 128)), .mov .r9 (.mem (stk 136)),
    .mov .r10 (.mem (stk 144)), .mov .r11 (.mem (stk 152)),
    .alu .and .r8 (.imm (BitVec.ofInt 32 (-8))),
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 62 - 1)), .alu .and .r11 (.reg .rcx),
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 62)), .alu .or .r11 (.reg .rcx)]

def prefixWord (i : Nat) : List Instr :=
  [.mov .rax (.mem (stk (160 + 8 * i))), .store (stk (32 + 8 * i)) .rax]

def saveSecret : List Instr := pruneRegs ++ pkPruneStores ++ (List.range 4).flatMap prefixWord

def hashNonce (f : Callee) (suffix : String) : Prog isa :=
  .seq init (.seq (update f suffix prefixArgs)
    (.seq (update f suffix (messageArgs 32)) (finalize f suffix 32 true)))

def reduceArgs (out : Nat) : List Instr :=
  framePtr .rdi out ++ framePtr .rsi 128 ++ [.mov .rdx (.mem (stk fScratch))]

def reduce (out : Nat) : Prog isa :=
  callWith (reduceArgs out) "vg_ed25519_scalar_reduce" scalarReduce

def baseArgs : List Instr :=
  ([.mov .rdi (.mem (stk fOut))] : List Instr) ++ framePtr .rsi 64 ++ [.mov .rdx (.mem (stk fScratch))]

def hashChallenge (f : Callee) (suffix : String) : Prog isa :=
  .seq init (.seq (update f suffix (inputArgs fOut 0))
    (.seq (update f suffix (inputArgs fPublicKey 32))
    (.seq (update f suffix (messageArgs 64)) (finalize f suffix 64 true))))

def mulAddArgs : List Instr :=
  ([.mov .rdi (.mem (stk fOut)), .alu .add .rdi (.imm 32)] : List Instr) ++
    framePtr .rsi 64 ++ framePtr .rdx 96 ++ framePtr .rcx 0 ++ [.mov .r8 (.mem (stk fScratch))]

def wipe : List Instr :=
  ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++ (List.range 24).map (fun i => .store (stk (8 * i)) .rax)

def body (f : Callee) (suffix : String) : Prog isa :=
  .seq (hashSeed f suffix) (.seq (.block saveSecret)
    (.seq (hashNonce f suffix) (.seq (reduce 64)
    (.seq (callWith baseArgs scalarBaseName scalarBase_precomputed)
    (.seq (hashChallenge f suffix) (.seq (reduce 96)
    (.seq (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) (.block wipe))))))))

def code (f : Callee) (suffix : String) : Prog isa :=
  .frame (.push ([.rdi, .rsi, .rdx, .rcx, .r8, .r9] ++ List.replicate 25 .rax))
    (body f suffix) (.pop .rax 31)

end VG.Impl.Ed25519.X86_64.SignCached

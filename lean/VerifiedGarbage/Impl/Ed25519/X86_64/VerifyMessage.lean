import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey
import VerifiedGarbage.Impl.Ed25519.X86_64.Scalar
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify

/-!
# Complete Ed25519 verification on x86-64

Hash `R || A || message`, reduce the digest modulo L, and call the existing
equation checker with the reduced scalar zero-extended to 64 bytes. The
SHA-512 calls use the supplied compression implementation and suffix.

The frame contains the 64-byte challenge and 64-byte digest, then the saved scratch,
signature, message length, message and public-key arguments. Both hash buffers
must be outside scratch because reduction and equation checking overwrite
scratch. The SHA-512 state and working space use the same scratch layout
as public-key derivation. The return value survives the frame pop.

The complete-operation proof targets `Spec.Ed25519.verifyContract`.
-/

namespace VG.Impl.Ed25519.X86_64.VerifyMessage

open VG.X86_64
open VG.Impl.Sha512.X86_64.Stream (Callee)

def fScratch : Nat := 128
def fSignature : Nat := 136
def fLength : Nat := 144
def fMessage : Nat := 152
def fPublicKey : Nat := 160

/-- Address an object in scratch through the saved pointer. -/
def scrPtr (r : Reg) (offset : Nat) : List Instr :=
  [.mov r (.mem (stk fScratch)), .alu .add r (.imm (BitVec.ofNat 32 offset))]

def initArgs : List Instr := [.mov .rdi (.mem (stk fScratch))]

/-- Hash the first 32 signature bytes (R), then the 32-byte public key. -/
def prefixArgs (source count : Nat) : List Instr :=
  ([.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm (BitVec.ofNat 32 count)),
    .mov .rdx (.mem (stk source)), .mov32 .rcx (.imm 32)] : List Instr) ++
    scrPtr .r8 shaScratch

def messageArgs : List Instr :=
  ([.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm 64),
    .mov .rdx (.mem (stk fMessage)), .mov .rcx (.mem (stk fLength))] : List Instr) ++
    scrPtr .r8 shaScratch

def finalizeArgs : List Instr :=
  ([.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fLength)),
    .alu .add .rsi (.imm 64), .mov .rdx (.reg .rsp),
    .alu .add .rdx (.imm 64)] : List Instr) ++ scrPtr .rcx shaScratch

/-- Produce the 64-byte digest in the frame at `rsp + 64`. -/
def hash (f : Callee) (suffix : String) : Prog isa :=
  .seq (callWith initArgs Spec.Sha512.init512Api.name
      (Sha512.X86_64.Stream.init Spec.Sha512.H0_512))
    (.seq (callWith (prefixArgs fSignature 0) (Spec.Sha512.updateApi.name ++ suffix)
      (Sha512.X86_64.Stream.update f))
    (.seq (callWith (prefixArgs fPublicKey 32) (Spec.Sha512.updateApi.name ++ suffix)
      (Sha512.X86_64.Stream.update f))
    (.seq (callWith messageArgs (Spec.Sha512.updateApi.name ++ suffix)
      (Sha512.X86_64.Stream.update f))
      (callWith finalizeArgs (Spec.Sha512.finalizeApi.name ++ suffix)
        (Sha512.X86_64.Stream.finalize f)))))

def reduceArgs : List Instr :=
  [.mov .rdi (.reg .rsp), .mov .rsi (.reg .rsp), .alu .add .rsi (.imm 64),
    .mov .rdx (.mem (stk fScratch))]

/-- The equation checker's challenge remains a 64-byte integer. -/
def extendChallenge : List Instr :=
  [.alu32 .xor .rax (.reg .rax), .store (stk 32) .rax, .store (stk 40) .rax,
    .store (stk 48) .rax, .store (stk 56) .rax]

def equationArgs : List Instr :=
  [.mov .rdi (.mem (stk fPublicKey)), .mov .rsi (.mem (stk fSignature)),
    .mov .rdx (.reg .rsp), .mov .rcx (.mem (stk fScratch))]

def body (fld : Arith) (dbl : Prog isa) (fs : String) (f : Callee) (suffix : String) : Prog isa :=
  .seq (hash f suffix)
    (.seq (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce)
    (.seq (.block extendChallenge)
      (callWith equationArgs ("vg_ed25519_verify_equation" ++ fs) (verifyEquation fld dbl))))

/-- Five saved arguments and sixteen hash/scalar words; calls use 16 more bytes.
The field multiplications are `fld` and the doublings `dbl`, those of
`vg_ed25519_verify_equation` with the suffix `fs`. -/
def code (fld : Arith) (dbl : Prog isa) (fs : String) (f : Callee) (suffix : String) : Prog isa :=
  .frame (.push [.rdi, .rsi, .rdx, .rcx, .r8,
    .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax,
    .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax])
    (body fld dbl fs f suffix) (.pop .r11 21)

end VG.Impl.Ed25519.X86_64.VerifyMessage

import VerifiedGarbage.Impl.TripleDes.X86_64.Block

/-!
# Triple DES ECB on x86-64

The block functions preserve all three pointers and callee-saved registers.
The ECB caller keeps the remaining count in rbp, outside the block's
512-byte scratch region. It accepts empty input, calls the block operation
once per block, and never adds or removes padding.
-/

namespace VG.Impl.TripleDes.X86_64.Ecb

open VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def save : List Instr := [.store (memOp .rcx 512) .rbp]
def setup : List Instr :=
  [rr .rbp .rdx, rr .rdx .rcx, .alu .cmp .rbp (.imm 0)]
def restore : List Instr := [.mov .rbp (.mem (memOp .rdx 512))]

def blockCall (direction : Direction) : Prog isa :=
  match direction with
  | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
  | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock

def advance : List Instr := [.alu .add .rsi (.imm 8), .alu .sub .rbp (.imm 1)]

def ecb (direction : Direction) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite .e (.block []) (.loop (.seq (blockCall direction) (.block advance)) .ne))
      (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.X86_64.Ecb

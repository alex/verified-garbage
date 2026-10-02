import VerifiedGarbage.Impl.TripleDes.AArch64.Block

namespace VG.Impl.TripleDes.AArch64.Ecb

open VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

def save : List Instr := [.str .x .x23 .x3 512, .str .x .x30 .x3 520]
def setup : List Instr := [rr .x23 .x2, rr .x2 .x3]
def restore : List Instr := [.ldr .x .x23 .x2 512, .ldr .x .x30 .x2 520]

def blockCall (d : Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
  | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock

def advance : List Instr := [.addImm .x .x1 .x1 8, .subImm .x .x23 .x23 1]

def ecb (d : Direction) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .x .x23) (.block [])
      (.loop (.seq (blockCall d) (.block advance)) (.nonzero .x .x23))) (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.AArch64.Ecb

import VerifiedGarbage.Impl.TripleDes.Arm.Block
namespace VG.Impl.TripleDes.Arm.Ecb
open VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)
def save : List Instr := [.str .lr .r3 512]
def setup : List Instr := [rr .r12 .r3, rr .r3 .r2, rr .r2 .r12, .cmp .r3 (.imm 0)]
def restore : List Instr := [.ldr .lr .r2 512]
def blockCall (d : Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
  | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock
def advance : List Instr := [.dp .add .r1 .r1 (.imm 8), .subs .r3 .r3 (.imm 1)]
def ecb (d : Direction) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .eq (.block [])
    (.loop (.seq (blockCall d) (.block advance)) .ne)) (.block restore))
def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt
end VG.Impl.TripleDes.Arm.Ecb

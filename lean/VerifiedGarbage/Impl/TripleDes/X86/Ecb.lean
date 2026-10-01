import VerifiedGarbage.Impl.TripleDes.X86.Block
namespace VG.Impl.TripleDes.X86.Ecb
open VG.X86 VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction)

def save : List Instr := savedRegs.zipIdx.map fun (r, i) => .store (memOp .eax (512 + 4 * i)) r
def setup : List Instr :=
  [rr .ebp .eax, .mov .ebx (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8)),
    .mov .edi (.mem (memOp .esp 12)), .alu .cmp .edi (.imm 0)]
def restore : List Instr := [rr .eax .ebp] ++
  savedRegs.zipIdx.map fun (r, i) => .mov r (.mem (memOp .eax (512 + 4 * i)))
def blockCall (d : Direction) : Prog isa :=
  .frame (.push [.ebp, .esi, .ebx])
    (match d with
    | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
    | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock)
    (.pop .eax 3)
def advance : List Instr := [.alu .add .esi (.imm 8), .alu .sub .edi (.imm 1)]
def ecb (d : Direction) : Prog isa :=
  .seq (.block [.mov .eax (.mem (memOp .esp 16))])
    (.seq (.block (save ++ setup))
      (.seq (.ite .e (.block []) (.loop (.seq (blockCall d) (.block advance)) .ne)) (.block restore)))
def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt
end VG.Impl.TripleDes.X86.Ecb

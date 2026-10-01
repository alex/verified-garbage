import VerifiedGarbage.Impl.TripleDes.X86.Block
namespace VG.Impl.TripleDes.X86.Key
open VG.X86 VG.Impl.TripleDes.X86

def save : List Instr :=
  [.mov .eax (.mem (memOp .esp 16))] ++
    savedRegs.zipIdx.map (fun (r, i) => .store (memOp .eax (4 * i)) r) ++ [rr .ebp .eax]
def restore : List Instr := blockRestore
def load (offset component : Nat) : List Instr :=
  [.mov .edx (.mem (memOp .esp 4)), .mov .edi (.mem (memOp .edx offset)),
    .mov .esi (.mem (memOp .edx (offset + 4))), .bswap .edi, .bswap .esi] ++
    permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx ++
    [rr .esi .ebx, rr .edi .eax, imm .eax 0, .store (memOp .ebp 20) .eax,
      .mov .eax (.mem (memOp .esp 12)),
      .alu .add .eax (.imm (BitVec.ofNat 32 (128 * component))), .store (memOp .ebp 16) .eax]
def rotate28 (r : Reg) (n : Nat) : List Instr :=
  [rr .eax r, .shift .shr .eax (28 - n), .shift .ror r (32 - n),
    .alu .xor r (.reg .eax), .alu .and r (.imm 268435455)]
def rotate (n : Nat) : Prog isa := .block (rotate28 .esi n ++ rotate28 .edi n)
def rotation : Prog isa :=
  .seq (.block [.mov .eax (.mem (memOp .ebp 20)), .alu .cmp .eax (.imm 2)])
    (.ite .b (rotate 1)
      (.seq (.block [.alu .cmp .eax (.imm 8)]) (.ite .e (rotate 1)
        (.seq (.block [.alu .cmp .eax (.imm 15)]) (.ite .e (rotate 1) (rotate 2))))))
def storeRound : List Instr :=
  permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx ++
    [.mov .edx (.mem (memOp .ebp 16)), .store (memOp .edx 0) .eax,
      .store (memOp .edx 4) .ebx, .alu .add .edx (.imm 8), .store (memOp .ebp 16) .edx,
      .mov .eax (.mem (memOp .ebp 20)), .alu .add .eax (.imm 1),
      .store (memOp .ebp 20) .eax, .alu .cmp .eax (.imm 16)]
def component (offset index : Nat) : Prog isa :=
  .seq (.block (load offset index)) (.loop (.seq rotation (.block storeRound)) .ne)
def copyThird : List Instr :=
  [.mov .edx (.mem (memOp .esp 12))] ++ (List.range 32).flatMap fun j =>
    [.mov .eax (.mem (memOp .edx (4 * j))), .store (memOp .edx (256 + 4 * j)) .eax]
def expandKey : Prog isa :=
  .seq (.block save) (.seq (component 0 0) (.seq (component 8 1)
    (.seq (.block [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)])
      (.seq (.ite .e (.block copyThird) (component 16 2)) (.block restore)))))
end VG.Impl.TripleDes.X86.Key

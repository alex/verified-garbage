import VerifiedGarbage.Impl.TripleDes.X86.Block
namespace VG.Impl.TripleDes.X86.Key
open VG.X86 VG.Impl.TripleDes.X86

def save : List Instr := saveWithArg 4
def restore : List Instr := blockRestore
def loadHead (offset : Nat) : List Instr :=
  [.mov .edx (.mem (memOp .esp 4)), .mov .edi (.mem (memOp .edx offset)),
    .mov .esi (.mem (memOp .edx (offset + 4))), .bswap .edi, .bswap .esi]
def loadTail (component : Nat) : List Instr :=
  [rr .esi .ebx, rr .edi .eax, .mov .edx (.mem (memOp .esp 12)),
    imm .eax 0, .store (memOp .ebp 20) .eax,
    .alu .add .edx (.imm (BitVec.ofNat 32 (128 * component))), .store (memOp .ebp 16) .edx]
def load (offset component : Nat) : List Instr :=
  loadHead offset ++ permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx ++
    loadTail component
def rotate28 (r : Reg) (n : Nat) : List Instr :=
  [rr .eax r, .shift .shr .eax (28 - n), .shift .ror r (32 - n),
    .alu .xor r (.reg .eax), .alu .and r (.imm 268435455)]
def rotate (n : Nat) : Prog isa := .block (rotate28 .esi n ++ rotate28 .edi n)
def rotation : Prog isa :=
  .seq (.block [.mov .eax (.mem (memOp .ebp 20)), .alu .cmp .eax (.imm 2)])
    (.ite .b (rotate 1)
      (.seq (.block [.alu .cmp .eax (.imm 8)]) (.ite .e (rotate 1)
        (.seq (.block [.alu .cmp .eax (.imm 15)]) (.ite .e (rotate 1) (rotate 2))))))
def storeTail : List Instr :=
  [.mov .edx (.mem (memOp .ebp 16)), .mov .ecx (.mem (memOp .ebp 20)),
    .store (memOp .edx 0) .eax, .store (memOp .edx 4) .ebx,
    .alu .add .edx (.imm 8), .store (memOp .ebp 16) .edx,
    .alu .add .ecx (.imm 1), .store (memOp .ebp 20) .ecx, .alu .cmp .ecx (.imm 16)]
def storeRound : List Instr :=
  permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx ++ storeTail
def component (offset index : Nat) : Prog isa :=
  .seq (.block (load offset index)) (.loop (.seq rotation (.block storeRound)) .ne)
def copyWords (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .eax (.mem (memOp .edx (4 * j))), .store (memOp .edx (256 + 4 * j)) .eax]
def copyThird : List Instr := [.mov .edx (.mem (memOp .esp 12))] ++ copyWords 32
def expandKey : Prog isa :=
  .seq (.block save) (.seq (component 0 0) (.seq (component 8 1)
    (.seq (.block [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)])
      (.seq (.ite .e (.block copyThird) (component 16 2)) (.block restore)))))
end VG.Impl.TripleDes.X86.Key

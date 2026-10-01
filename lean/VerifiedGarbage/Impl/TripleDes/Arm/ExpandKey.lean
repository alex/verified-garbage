import VerifiedGarbage.Impl.TripleDes.Arm.Common
namespace VG.Impl.TripleDes.Arm.Key
open VG.Arm VG.Impl.TripleDes.Arm

def savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]
def save : List Instr := savedRegs.zipIdx.map fun (r, i) => .str r .r3 (4 * i)
def restore : List Instr := savedRegs.zipIdx.map fun (r, i) => .ldr r .r3 (4 * i)

def load (offset component : Nat) : List Instr :=
  [.ldr .r4 .r0 offset, .ldr .r5 .r0 (offset + 4), .rev .r4 .r4, .rev .r5 .r5] ++
    permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr ++
    [imm .r9 0, .dp .add .r8 .r2 (.imm (BitVec.ofNat 32 (128 * component)))]

def rotate28 (r : Reg) (n : Nat) : List Instr :=
  [.mov .r4 (.shifted r .lsr (28 - n)), .mov r (.shifted r .ror (32 - n)),
    .dp .eor r r (.reg .r4)] ++ mask r 28

def rotate (n : Nat) : Prog isa := .block (rotate28 .r10 n ++ rotate28 .r11 n)
def rotation : Prog isa :=
  .seq (.block [.mov .r4 (.shifted .r9 .lsr 1), .cmp .r4 (.imm 0)]) (.ite .eq (rotate 1)
    (.seq (.block [.cmp .r9 (.imm 8)]) (.ite .eq (rotate 1)
      (.seq (.block [.cmp .r9 (.imm 15)]) (.ite .eq (rotate 1) (rotate 2))))))

def storeRound : List Instr :=
  permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr ++
    [.str .r4 .r8 0, .str .r5 .r8 4, .dp .add .r8 .r8 (.imm 8),
      .dp .add .r9 .r9 (.imm 1), .cmp .r9 (.imm 16)]
def component (offset index : Nat) : Prog isa :=
  .seq (.block (load offset index)) (.loop (.seq rotation (.block storeRound)) .ne)
def copyThird : List Instr :=
  (List.range 16).flatMap fun j =>
    [.ldr .r4 .r2 (8 * j), .ldr .r5 .r2 (8 * j + 4),
      .str .r4 .r2 (256 + 8 * j), .str .r5 .r2 (256 + 8 * j + 4)]
def expandKey : Prog isa :=
  .seq (.block save) (.seq (component 0 0) (.seq (component 8 1)
    (.seq (.block [.cmp .r1 (.imm 16)])
      (.seq (.ite .eq (.block copyThird) (component 16 2)) (.block restore)))))
end VG.Impl.TripleDes.Arm.Key

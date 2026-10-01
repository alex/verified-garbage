import VerifiedGarbage.Impl.TripleDes.X86_64.Common

/-!
# Scalar Triple DES key expansion on x86-64

PC-1 and PC-2 use fixed permutations. The only branches depend on key
length or the public round counter. The sixteen 28-bit rotations are
selected by FIPS 46-3's schedule; no secret-indexed table is read. Registers
r12/r13 hold C/D; r14 is the round counter and r15 the output pointer.
The three schedules are stored in the specification's canonical layout.
-/

namespace VG.Impl.TripleDes.X86_64.Key

open VG.X86_64 VG.Impl.TripleDes.X86_64

def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

def save : List Instr :=
  savedRegs.zipIdx.map fun (r, i) => .store (memOp .rcx (8 * i)) r

def restore : List Instr :=
  savedRegs.zipIdx.map fun (r, i) => .mov r (.mem (memOp .rcx (8 * i)))

def load (offset component : Nat) : List Instr :=
  [.mov .rax (.mem (memOp .rdi offset)), .bswap .rax] ++
    permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp ++
    [rr .r12 .rbx, .shift .shr .r12 28, rr .r13 .rbx,
     .alu .and .r13 (.imm 0x0fffffff), imm .r14 0, rr .r15 .rdx,
     .alu .add .r15 (.imm (BitVec.ofNat 32 (128 * component)))]

def rotate28 (r : Reg) (n : Nat) : List Instr :=
  [rr .rax r, .shift .shr .rax (28 - n), .shift .ror r (64 - n),
   .alu .xor r (.reg .rax), .alu .and r (.imm 0x0fffffff)]

def rotate (n : Nat) : Prog isa := .block (rotate28 .r12 n ++ rotate28 .r13 n)

/-- Rounds 1, 2, 9 and 16 rotate by one; the other rounds by two. -/
def rotation : Prog isa :=
  .seq (.block [.alu .cmp .r14 (.imm 2)])
    (.ite .b (rotate 1)
      (.seq (.block [.alu .cmp .r14 (.imm 8)])
        (.ite .e (rotate 1)
          (.seq (.block [.alu .cmp .r14 (.imm 15)]) (.ite .e (rotate 1) (rotate 2))))))

def storeRound : List Instr :=
  [rr .rax .r12, .shift .ror .rax 36, .alu .xor .rax (.reg .r13)] ++
    permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp ++
    [.store (memOp .r15 0) .rbx, .alu .add .r15 (.imm 8),
     .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm 16)]

def component (offset index : Nat) : Prog isa :=
  .seq (.block (load offset index)) (.loop (.seq rotation (.block storeRound)) .ne)

/-- EDE2 reuses the first schedule rather than expanding K1 again. -/
def copyThird : List Instr :=
  (List.range 16).flatMap fun j =>
    [.mov .rax (.mem (memOp .rdx (8 * j))), .store (memOp .rdx (256 + 8 * j)) .rax]

def expandKey : Prog isa :=
  .seq (.block save)
    (.seq (component 0 0)
      (.seq (component 8 1)
        (.seq (.block [.alu .cmp .rsi (.imm 16)])
          (.seq (.ite .e (.block copyThird) (component 16 2)) (.block restore)))))

end VG.Impl.TripleDes.X86_64.Key

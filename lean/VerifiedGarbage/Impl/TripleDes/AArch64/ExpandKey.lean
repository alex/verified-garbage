import VerifiedGarbage.Impl.TripleDes.AArch64.Common

namespace VG.Impl.TripleDes.AArch64.Key

open VG.AArch64 VG.Impl.TripleDes.AArch64

def savedRegs : List Reg := [.x19, .x20, .x21, .x22]

def save : List Instr := savedRegs.zipIdx.map fun (r, i) => .str .x r .x3 (8 * i)
def restore : List Instr := savedRegs.zipIdx.map fun (r, i) => .ldr .x r .x3 (8 * i)

def load (offset component : Nat) : List Instr :=
  [.ldr .x .x4 .x0 offset, .rev .x4 .x4] ++
    permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7 ++
    [.lsr .x .x19 .x5 28, rr .x20 .x5] ++ mask .x20 28 ++
    [imm .x21 0, .addImm .x .x22 .x2 (128 * component)]

def rotate28 (r : Reg) (n : Nat) : List Instr :=
  [.lsr .x .x4 r (28 - n), .ror .x r r (64 - n), .logic .eor .x r r .x4] ++ mask r 28

def rotate (n : Nat) : Prog isa := .block (rotate28 .x19 n ++ rotate28 .x20 n)

def rotation : Prog isa :=
  .seq (.block [.lsr .x .x4 .x21 1])
    (.ite (.zero .x .x4) (rotate 1)
      (.seq (.block [.subImm .x .x4 .x21 8])
        (.ite (.zero .x .x4) (rotate 1)
          (.seq (.block [.subImm .x .x4 .x21 15])
            (.ite (.zero .x .x4) (rotate 1) (rotate 2))))))

def storeRound : List Instr :=
  [.lsl .x .x4 .x19 28, .logic .eor .x .x4 .x4 .x20] ++
    permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7 ++
    [.str .x .x5 .x22 0, .addImm .x .x22 .x22 8, .addImm .x .x21 .x21 1,
      .subImm .x .x4 .x21 16]

def component (offset index : Nat) : Prog isa :=
  .seq (.block (load offset index)) (.loop (.seq rotation (.block storeRound)) (.nonzero .x .x4))

def copyThird : List Instr :=
  (List.range 16).flatMap fun j => [.ldr .x .x4 .x2 (8 * j), .str .x .x4 .x2 (256 + 8 * j)]

def expandKey : Prog isa :=
  .seq (.block save)
    (.seq (component 0 0)
      (.seq (component 8 1)
        (.seq (.block [.subImm .x .x4 .x1 16])
          (.seq (.ite (.zero .x .x4) (.block copyThird) (component 16 2)) (.block restore)))))

end VG.Impl.TripleDes.AArch64.Key

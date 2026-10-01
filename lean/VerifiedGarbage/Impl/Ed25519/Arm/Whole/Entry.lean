import VerifiedGarbage.TCB.Arm.Isa

namespace VG.Impl.Ed25519.Arm.Whole
open VG.Arm

def argReg (j : Nat) : Reg :=
  match j with | 0 => .r0 | 1 => .r1 | 2 => .r2 | _ => .r3

def saveWord (j : Nat) : List Instr :=
  (if j < 4 then [] else [.ldrSp .lr (280 + 4 * (j - 4))]) ++
    [.addSp .r12 248, .str (if j < 4 then argReg j else .lr) .r12 (4 * j)]

def saveArgs (n : Nat) : List Instr := (List.range n).flatMap saveWord

def wrap (n : Nat) (body : Prog isa) : Prog isa :=
  .frame (.push [.lr])
    (.frame (.push [.r12])
      (.frame (.alloc 24)
        (.frame (.alloc 248) (.seq (.block (saveArgs n)) body) (.free 248))
        (.free 24))
      (.pop .r12 4))
    (.pop .lr 4)

end VG.Impl.Ed25519.Arm.Whole

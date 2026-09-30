import VerifiedGarbage.Impl.Rc2.Arm.Lookup

/-! # RC2 key expansion on ARMv7

Public lengths control the loops. `lr` holds public addresses; all
callee-saved registers are saved in the scratch buffer supplied on the stack.
PITABLE scans never branch on key bytes.
-/

namespace VG.Impl.Rc2.Arm

open VG.Arm

def saved : List Reg := [.r8, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .lr]

def save (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .str r base (offset + 4 * i)

def restore (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .ldr r base (offset + 4 * i)

def copyKey : List Instr :=
  [.dp .add .lr .r4 (.reg .r0), .ldrb .r12 .lr 0,
   .dp .add .lr .r6 (.reg .r0), .strb .r12 .lr 0,
   .dp .add .r0 .r0 (.imm 1), .cmp .r0 (.reg .r5)]

def fillInput : List Instr :=
  [.dp .add .lr .r6 (.reg .r0), .dp .sub .lr .lr (.imm 1), .ldrb .r12 .lr 0,
   .dp .sub .r9 .r0 (.reg .r5), .dp .add .lr .r6 (.reg .r9), .ldrb .r3 .lr 0,
   .dp .add .r12 .r12 (.reg .r3)]

def storeKey : List Instr := [.dp .add .lr .r6 (.reg .r0), .strb .r12 .lr 0]

def fillFinish : List Instr :=
  storeKey ++ [.dp .add .r0 .r0 (.imm 1), .cmp .r0 (.imm 128)]

def fillKey : List Instr := fillInput ++ piLookup ++ fillFinish

def maskCode : Prog isa :=
  .seq (.block ([rr .r9 .r7] ++ mask .r9 3 ++ [imm .r2 255]))
    ((List.range 7).foldr (fun i rest =>
      .seq (.block [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .eq (.block [imm .r2 (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))

def reduceInput : List Instr :=
  [.dp .add .lr .r6 (.reg .r0), .ldrb .r12 .lr 0, .dp .and .r12 .r12 (.reg .r2)]

def reduceKey : List Instr := reduceInput ++ piLookup ++ storeKey

def descendInput : List Instr :=
  [.dp .sub .r0 .r0 (.imm 1), .dp .add .lr .r6 (.reg .r0), .dp .add .lr .lr (.imm 1),
   .ldrb .r12 .lr 0, .dp .add .r9 .r0 (.reg .r1),
   .dp .add .lr .r6 (.reg .r9), .ldrb .r3 .lr 0, .dp .eor .r12 .r12 (.reg .r3)]

def descendKey : List Instr :=
  descendInput ++ piLookup ++ (storeKey ++ [.cmp .r0 (.imm 0)])

def expandCopyFill : Prog isa :=
  .seq (.loop (.block copyKey) .ne)
    (.seq (.block [.cmp .r0 (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block [])))

def reduceSetup : List Instr :=
  [.dp .add .r1 .r7 (.imm 7), .mov .r1 (.shifted .r1 .lsr 3), imm .r0 128,
   .dp .sub .r0 .r0 (.reg .r1)]

def expandReduce : Prog isa :=
  .seq (.block reduceSetup)
    (.seq maskCode
      (.seq (.block reduceKey)
        (.seq (.block [.cmp .r0 (.imm 0)])
          (.ite .ne (.loop (.block descendKey) .ne) (.block [])))))

def expandKey : Prog isa :=
  .seq (.block [.ldrSp .r12 0])
    (.seq (.block (save .r12 0 ++
        [rr .r8 .r12, rr .r4 .r0, rr .r5 .r1, rr .r6 .r3, rr .r7 .r2, imm .r0 0]))
      (.seq expandCopyFill (.seq expandReduce (.block ([rr .r12 .r8] ++ restore .r12 0)))))

end VG.Impl.Rc2.Arm

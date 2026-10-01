import VerifiedGarbage.Impl.Rc2.AArch64.Lookup

/-! # RC2 key expansion on baseline AArch64

The public lengths control the loops. `x9` holds public addresses and
`x10` holds public comparison results; PITABLE scans never branch on key bytes.
-/

namespace VG.Impl.Rc2.AArch64

open VG.AArch64

def saved : List Reg := [.x23, .x24, .x19, .x20, .x21, .x22]

def save (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .str .x r base (offset + 8 * i)

def restore (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .ldr .x r base (offset + 8 * i)

def copyKey : List Instr :=
  [.add .x .x9 .x19 .x23, .ldrb .x8 .x9 0,
   .add .x .x9 .x21 .x23, .strb .x8 .x9 0,
   .addImm .x .x23 .x23 1, .sub .x .x10 .x23 .x20]

def fillInput : List Instr :=
  [.add .x .x9 .x21 .x23, .subImm .x .x9 .x9 1, .ldrb .x8 .x9 0,
   .sub .x .x5 .x23 .x20, .add .x .x9 .x21 .x5, .ldrb .x3 .x9 0,
   .add .x .x8 .x8 .x3]

def storeKey : List Instr := [.add .x .x9 .x21 .x23, .strb .x8 .x9 0]

def fillFinish : List Instr :=
  storeKey ++ [.addImm .x .x23 .x23 1, .subImm .x .x10 .x23 128]

def fillKey : List Instr := fillInput ++ piLookup ++ fillFinish

def maskCode : Prog isa :=
  .seq (.block ([rr .x5 .x22] ++ mask .x5 3 ++ [imm .x2 255]))
    ((List.range 7).foldr (fun i rest =>
      .seq (.block [.subImm .x .x10 .x5 (i + 1)])
        (.seq (.ite (.zero .x .x10) (.block [imm .x2 (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))

def reduceInput : List Instr :=
  [.add .x .x9 .x21 .x23, .ldrb .x8 .x9 0, .logic .and .x .x8 .x8 .x2]

def reduceKey : List Instr := reduceInput ++ piLookup ++ storeKey

def descendInput : List Instr :=
  [.subImm .x .x23 .x23 1, .add .x .x9 .x21 .x23, .addImm .x .x9 .x9 1,
   .ldrb .x8 .x9 0, .add .x .x5 .x23 .x24,
   .add .x .x9 .x21 .x5, .ldrb .x3 .x9 0, .logic .eor .x .x8 .x8 .x3]

def descendKey : List Instr :=
  descendInput ++ piLookup ++ (storeKey ++ [rr .x10 .x23])

def expandCopyFill : Prog isa :=
  .seq (.loop (.block copyKey) (.nonzero .x .x10))
    (.seq (.block [.subImm .x .x10 .x23 128])
      (.ite (.nonzero .x .x10) (.loop (.block fillKey) (.nonzero .x .x10)) (.block [])))

def reduceSetup : List Instr :=
  [.addImm .x .x24 .x22 7, .lsr .x .x24 .x24 3, imm .x23 128, .sub .x .x23 .x23 .x24]

def expandReduce : Prog isa :=
  .seq (.block reduceSetup)
    (.seq maskCode
      (.seq (.block reduceKey)
        (.seq (.block [rr .x10 .x23])
          (.ite (.nonzero .x .x10) (.loop (.block descendKey) (.nonzero .x .x10)) (.block [])))))

def expandKey : Prog isa :=
  .seq (.block (save .x4 0 ++
      [rr .x19 .x0, rr .x20 .x1, rr .x21 .x3, rr .x22 .x2, imm .x23 0]))
    (.seq expandCopyFill (.seq expandReduce (.block (restore .x4 0))))

end VG.Impl.Rc2.AArch64

import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar

/-! Full-width scalar multiply-add followed by subgroup reduction. -/

namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def wideAccumulate (a b : Nat) : List Instr :=
  [.movz .w .x10 0 0] ++ row a b 0 ++ row a b 1 ++ row a b 2 ++ row a b 3

def mulAddSave : List Instr := saved.map fun (r, d) => .str .x r .x4 d

def loadWords (src : Reg) : List Instr :=
  [.ldr .x .x4 src 0, .ldr .x .x5 src 8, .ldr .x .x6 src 16, .ldr .x .x7 src 24]

def copyScalar (src : Reg) (dst : Nat) : List Instr := loadWords src ++ store4 dst

def storeWide : List Instr := stores 128 .x4 .x5 .x6 .x7 ++ stores 160 .x21 .x22 .x23 .x24

def reduceArgs : List Instr := [.addImm .x .x1 .x0 128, mov .x2 .x0, mov .x0 .x19]

def mulAddSetup : List Instr :=
  mulAddSave ++ [mov .x19 .x0, mov .x0 .x4] ++
    copyScalar .x2 64 ++ copyScalar .x3 96 ++ loadWords .x1

/-- `(out, r, k, s, scratch) = (x0, x1, x2, x3, x4)`. -/
def scalarMulAdd : Prog isa :=
  .seq (.block mulAddSetup) <|
  .seq (.block (wideAccumulate 64 96)) <|
  .seq (.block (storeWide ++ reduceArgs ++ scalarInit)) <|
  .seq (.loop (.block scalarByte) (.nonzero .x .x19)) (.block scalarFinish)

end VG.Impl.Ed25519.AArch64

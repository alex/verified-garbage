import VerifiedGarbage.Impl.Ed25519.X86_64.Scalar

/-!
# Ed25519 scalar multiply-add: wide multiplication

The product is kept at its full 512-bit width until subgroup reduction.
It reuses the same integer multiply-accumulate rows as field arithmetic,
without that arithmetic's reduction modulo the field prime.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64 VG.Impl.X25519.X86_64

/-- Accumulate a 256-by-256 product into the four input words in r8–r11.
The eight output words occupy r8–r15. -/
def wideAccumulate (a b : Nat) : List Instr :=
  row a b 0 ++ row a b 1 ++ row a b 2 ++ row a b 3

def wideMul (a b : Nat) : List Instr := zero4 ++ wideAccumulate a b

def mulAddSave : List Instr := saved.map fun (r, d) => .store (at_ .r8 d) r

def loadWords (src : Reg) : List Instr :=
  [.mov .r8 (.mem (at_ src 0)), .mov .r9 (.mem (at_ src 8)),
    .mov .r10 (.mem (at_ src 16)), .mov .r11 (.mem (at_ src 24))]

/-- Copy a 32-byte operand into the scratch area based at rdi. -/
def copyScalar (src : Reg) (dst : Nat) : List Instr := loadWords src ++ store4 dst

def loadScalar : List Instr := loadWords .rsi

def storeWide : List Instr := stores 128 .r8 .r9 .r10 .r11 ++ stores 160 .r12 .r13 .r14 .r15

def reduceArgs : List Instr :=
  [.mov .rsi (.reg .rdi), .alu .add .rsi (.imm 128), .store (at_ .rdi 48) .rbx]

def mulAddSetup : List Instr :=
  mulAddSave ++ [.mov .rbx (.reg .rdi), .mov .rdi (.reg .r8)] ++
    copyScalar .rdx 64 ++ copyScalar .rcx 96 ++ loadScalar

/-- `(out, r, k, s, scratch) = (rdi, rsi, rdx, rcx, r8)`.
The first four product words start at r; the multiply-accumulate rows then
add k*s. The reducer consumes this full 512-bit value from scratch. -/
def scalarMulAdd : Prog isa :=
  .seq (.block mulAddSetup) <|
  .seq (.block (wideAccumulate 64 96)) <|
  .seq (.block (storeWide ++ reduceArgs ++ zero4 ++ [.mov32 .rbx (.imm 64)])) <|
  .seq (.loop (.block scalarWord) .ne) <|
    .block (scalarFinishArgs ++ scalarRestore ++ [.store (at_ .rdi 0) .r8, .store (at_ .rdi 8) .r9,
      .store (at_ .rdi 16) .r10, .store (at_ .rdi 24) .r11])

end VG.Impl.Ed25519.X86_64

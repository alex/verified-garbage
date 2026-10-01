import VerifiedGarbage.Impl.Argon2.X86_64.Initial

/-!
# Argon2 memory initialization on x86-64

`rbp` addresses the derivation frame containing H₀ and the public arguments;
`rbx` addresses hash scratch. `r13` holds the lane length in blocks, as
computed by the parameter-setup layer. The complete matrix is cleared before
H′ initializes columns zero and one of every lane. This establishes exactly
`Spec.Argon2.initMemory` even when the allocation initially contains arbitrary
bytes. Each H′ call uses the supplied BLAKE2b backend.
-/

namespace VG.Impl.Argon2.X86_64.MemoryInit

open VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (at_ Hash)

/-- The memory pointer and allocated block count in the enclosing frame. -/
def memoryOffset : Nat := 232
def blocksOffset : Nat := 240

/-- Clear one word, advancing the destination and public countdown. -/
def clearWord : List Instr :=
  [.store (at_ .r14) .rcx, .alu .add .r14 (.imm 8), .alu .sub .rax (.imm 1)]

def clearHeader : List Instr :=
  [.mov .r14 (.mem (at_ .rbp memoryOffset)), .mov .rax (.mem (at_ .rbp blocksOffset)),
    .mov32 .rcx (.imm 0)]

def clearSetup : List Instr := clearHeader ++ List.replicate 7 (.alu .add .rax (.reg .rax))

def clearSetupCode : Prog isa := .block clearSetup

def clear : Prog isa := .seq clearSetupCode (.loop (.block clearWord) .ne)

/-- Reset the matrix pointer and lane number, retaining the lane stride in bytes. -/
def lanesHeader : List Instr :=
  [.mov .r14 (.mem (at_ .rbp memoryOffset)), .mov32 .r12 (.imm 0),
    .mov .r15 (.mem (at_ .rbp Initial.lanesOffset))]

def lanesSetup : List Instr := lanesHeader ++ List.replicate 10 (.alu .add .r13 (.reg .r13))

def lanesSetupCode : Prog isa := .block lanesSetup

/-- H′(1024, H₀ || LE32(column) || LE32(lane)). -/
def blockArgs (column : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 column)), .store32 (at_ .rbp 64) .rax,
    .store32 (at_ .rbp 68) .r12, .mov .rdi (.reg .rbp), .mov32 .rsi (.imm 72),
    .mov .rdx (.reg .r14), .mov32 .rcx (.imm 1024), .mov .r8 (.reg .rbx)]

def block (name : String) (h : Hash) (column : Nat) : Prog isa :=
  .seq (.block (blockArgs column)) (.call name (HPrime.code h))

/-- Initialize one lane, then advance to the next lane's first block. -/
def lane (name : String) (h : Hash) : Prog isa :=
  .seq (block name h 0)
  (.seq (.block [.alu .add .r14 (.imm 1024)])
  (.seq (block name h 1)
    (.block [.alu .add .r14 (.reg .r13), .alu .sub .r14 (.imm 1024),
      .alu .add .r12 (.imm 1), .alu .sub .r15 (.imm 1)])))

/-- Zero the matrix and initialize both leading blocks in every lane. -/
def code (name : String) (h : Hash) : Prog isa :=
  .seq clear (.seq lanesSetupCode (.loop (lane name h) .ne))

end VG.Impl.Argon2.X86_64.MemoryInit

import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Initial

/-!
# Argon2 memory initialization on ARM64

`x19` addresses the derivation frame containing H₀ and the public arguments;
`x24` addresses hash scratch. `x21` holds the lane length in blocks, as
computed by the parameter-setup layer. The complete matrix is cleared before
H′ initializes columns zero and one of every lane. This establishes exactly
`Spec.Argon2.initMemory` even when the allocation initially contains arbitrary
bytes. Each H′ call uses the supplied BLAKE2b backend.
-/

namespace VG.Impl.Argon2.AArch64.MemoryInit

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions
open VG.Impl.Argon2.AArch64.HPrime (Hash)

/-- The memory pointer and allocated block count in the enclosing frame. -/
def memoryOffset : Nat := 232
def blocksOffset : Nat := 240

/-- Clear one word, advancing the destination and public countdown. -/
def clearWord : List Instr :=
  [store .x22 0 .x3, addi .x22 8, subi .x8 1].flatten

def clearHeader : List Instr :=
  [load .x22 .x19 memoryOffset, load .x8 .x19 blocksOffset, imm .x3 0].flatten

def clearSetup : List Instr := clearHeader ++ (List.replicate 7 (add .x8 .x8)).flatten

def clearSetupCode : Prog isa := .block clearSetup

def clear : Prog isa := .seq clearSetupCode (.loop (.block clearWord) (.nonzero .x .x15))

/-- Reset the matrix pointer and lane number, retaining the lane stride in bytes. -/
def lanesHeader : List Instr :=
  [load .x22 .x19 memoryOffset, imm .x20 0, load .x23 .x19 Initial.lanesOffset].flatten

def lanesSetup : List Instr := lanesHeader ++ (List.replicate 10 (add .x21 .x21)).flatten

def lanesSetupCode : Prog isa := .block lanesSetup

/-- H′(1024, H₀ || LE32(column) || LE32(lane)). -/
def blockArgs (column : Nat) : List Instr :=
  [imm .x8 column, store32 .x19 64 .x8, store32 .x19 68 .x20, mov .x0 .x19, imm .x1 72, mov .x2 .x22, imm .x3 1024, mov .x4 .x24].flatten

def block (name : String) (h : Hash) (column : Nat) : Prog isa :=
  .seq (.block (blockArgs column)) (.call name (HPrime.code h))

/-- Initialize one lane, then advance to the next lane's first block. -/
def lane (name : String) (h : Hash) : Prog isa :=
  .seq (block name h 0)
  (.seq (.block [addi .x22 1024].flatten)
  (.seq (block name h 1)
    (.block [add .x22 .x21, subi .x22 1024, addi .x20 1, subi .x23 1].flatten)))

/-- Zero the matrix and initialize both leading blocks in every lane. -/
def code (name : String) (h : Hash) : Prog isa :=
  .seq clear (.seq lanesSetupCode (.loop (lane name h) (.nonzero .x .x15)))

end VG.Impl.Argon2.AArch64.MemoryInit

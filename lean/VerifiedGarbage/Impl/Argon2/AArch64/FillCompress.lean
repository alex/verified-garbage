import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Spec.Argon2.Contract

/-! Compress the selected previous/reference blocks and update the current
matrix cell. Pointer setup supplied `x6` (current), `x0` (previous), and
`x1` (reference). The derivation frame holds the pass at offset zero and
scratch pointer at offset 248; offset 16 retains the destination across G.
The first 4096 scratch bytes belong to G, and its output is at offset 4096.
-/

namespace VG.Impl.Argon2.AArch64.FillCompress

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def saveCurrent : List Instr := [store .x19 16 .x6].flatten

def compressArgs : List Instr := [load .x3 .x19 248, mov .x2 .x3, addi .x2 4096].flatten

def writeArgs : List Instr := [load .x0 .x19 16, load .x1 .x19 248, addi .x1 4096, load .x5 .x19 0].flatten

def operation : Prog isa :=
  .seq (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.AArch64.compress)
    (.seq (.block writeArgs) FillWrite.code)

def setup : Prog isa := .seq (.block saveCurrent) (.block compressArgs)

def code : Prog isa := .seq setup operation

end VG.Impl.Argon2.AArch64.FillCompress

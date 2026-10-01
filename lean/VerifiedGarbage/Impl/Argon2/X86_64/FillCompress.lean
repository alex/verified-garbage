import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite
import VerifiedGarbage.Spec.Argon2.Contract

/-! Compress the selected previous/reference blocks and update the current
matrix cell. Pointer setup supplied `r10` (current), `rdi` (previous), and
`rsi` (reference). The derivation frame holds the pass at offset zero and
scratch pointer at offset 248; offset 16 retains the destination across G.
The first 4096 scratch bytes belong to G, and its output is at offset 4096.
-/

namespace VG.Impl.Argon2.X86_64.FillCompress

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def saveCurrent : List Instr := [.store (at_ .rbp 16) .r10]

def compressArgs : List Instr := [
  .mov .rcx (.mem (at_ .rbp 248)), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 4096)]

def writeArgs : List Instr := [
  .mov .rdi (.mem (at_ .rbp 16)), .mov .rsi (.mem (at_ .rbp 248)),
  .alu .add .rsi (.imm 4096), .mov .r9 (.mem (at_ .rbp 0))]

def operation : Prog isa :=
  .seq (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.X86_64.compress)
    (.seq (.block writeArgs) FillWrite.code)

def code : Prog isa := .seq (.block saveCurrent) (.seq (.block compressArgs) operation)

end VG.Impl.Argon2.X86_64.FillCompress

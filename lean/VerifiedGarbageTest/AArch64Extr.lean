import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# AArch64 EXTR

Expected results below were produced by the corresponding EXTR instruction in
a Clang inline-assembly probe on an Apple M1 Max (macOS 27). The sources have
distinct upper and lower halves, so the 32-bit results check both truncation of
the inputs and zero-extension of the destination. The probes covered the
smallest and largest encodable amounts and some between, and destinations
aliasing each source. These are instruction-semantic checks, not cryptographic
known-answer vectors.
-/

namespace VG.Test.AArch64Extr
open AArch64

def input : State where
  gpr r := if r = .x1 then 0x0123456789abcdef else
    if r = .x2 then 0xfedcba9876543210 else 0xdeadbeefdeadbeef
  sp := 0x1000
  c := true
  mem _ := 0
  rd := []
  wr := []

def run (i : Instr) : Option (BitVec 64) := (exec i input).map (·.gpr .x0)

#guard run (.extr .x .x0 .x1 .x2 0) == some 0xfedcba9876543210
#guard run (.extr .x .x0 .x1 .x2 1) == some 0xff6e5d4c3b2a1908
#guard run (.extr .x .x0 .x1 .x2 8) == some 0xeffedcba98765432
#guard run (.extr .x .x0 .x1 .x2 56) == some 0x23456789abcdeffe
#guard run (.extr .x .x0 .x1 .x2 63) == some 0x02468acf13579bdf
#guard run (.extr .w .x0 .x1 .x2 0) == some 0x0000000076543210
#guard run (.extr .w .x0 .x1 .x2 1) == some 0x00000000bb2a1908
#guard run (.extr .w .x0 .x1 .x2 31) == some 0x0000000013579bde

-- Encodings outside the operand width are rejected, rather than masked.
#guard run (.extr .w .x0 .x1 .x2 32) == none
#guard run (.extr .x .x0 .x1 .x2 64) == none

-- Aliased destinations read the old sources before writing the result.
#guard (exec (.extr .x .x1 .x1 .x1 8) input).map (·.gpr .x1) == some 0xef0123456789abcd
#guard (exec (.extr .x .x1 .x1 .x2 56) input).map (·.gpr .x1) == some 0x23456789abcdeffe
#guard (exec (.extr .x .x2 .x1 .x2 56) input).map (·.gpr .x2) == some 0x23456789abcdeffe

-- No flags or optional CPU features, and the framework recognizes writes.
#guard (exec (.extr .x .x0 .x1 .x2 56) input).map (·.c) == some true
#guard Instr.requires (.extr .x .x0 .x1 .x2 56) == []
#guard dstOf (.extr .x .x0 .x1 .x2 56) == some .x0

#guard printer.instr (.extr .x .x0 .x1 .x2 56) == ["extr x0, x1, x2, #56"]
#guard printer.instr (.extr .w .x0 .x1 .x2 31) == ["extr w0, w1, w2, #31"]

-- The result is public exactly when both source operands are public.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.extr .x .x0 .x1 .x2 56)).map (AArch64.Taint.pub · .x0)) == some true
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1])
  (.extr .x .x0 .x1 .x2 56)).map (AArch64.Taint.pub · .x0)) == some false
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x2])
  (.extr .x .x0 .x1 .x2 56)).map (AArch64.Taint.pub · .x0)) == some false

end VG.Test.AArch64Extr

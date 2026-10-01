import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# AArch64 logical instructions with a rotated second register

Expected results below were produced by the corresponding AND/ORR/EOR/BIC
instruction in a Clang inline-assembly probe on an Apple M5 Max (macOS 27).
Each source has nonzero upper and lower halves, so the 32-bit results check
both truncation of the input and zero-extension of the destination. The
probes covered rotation zero, one, and the largest encodable amount.
These are instruction-semantic checks, not cryptographic known-answer vectors.
-/

namespace VG.Test.AArch64Logical
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

#guard run (.logicRor .and .x .x0 .x1 .x2 0) == some 0x0000000000000000
#guard run (.logicRor .and .x .x0 .x1 .x2 1) == some 0x01224544092a0908
#guard run (.logicRor .and .x .x0 .x1 .x2 63) == some 0x0121452088a84421
#guard run (.logicRor .and .w .x0 .x1 .x2 0) == some 0x0000000000000000
#guard run (.logicRor .and .w .x0 .x1 .x2 1) == some 0x00000000092a0908
#guard run (.logicRor .and .w .x0 .x1 .x2 31) == some 0x0000000088a84420
#guard run (.logicRor .orr .x .x0 .x1 .x2 0) == some 0xffffffffffffffff
#guard run (.logicRor .orr .x .x0 .x1 .x2 1) == some 0x7f6f5d6fbbabddef
#guard run (.logicRor .orr .x .x0 .x1 .x2 63) == some 0xfdbb7577edabedef
#guard run (.logicRor .orr .w .x0 .x1 .x2 0) == some 0x00000000ffffffff
#guard run (.logicRor .orr .w .x0 .x1 .x2 1) == some 0x00000000bbabddef
#guard run (.logicRor .orr .w .x0 .x1 .x2 31) == some 0x00000000edabedef
#guard run (.logicRor .eor .x .x0 .x1 .x2 0) == some 0xffffffffffffffff
#guard run (.logicRor .eor .x .x0 .x1 .x2 1) == some 0x7e4d182bb281d4e7
#guard run (.logicRor .eor .x .x0 .x1 .x2 63) == some 0xfc9a30576503a9ce
#guard run (.logicRor .eor .w .x0 .x1 .x2 0) == some 0x00000000ffffffff
#guard run (.logicRor .eor .w .x0 .x1 .x2 1) == some 0x00000000b281d4e7
#guard run (.logicRor .eor .w .x0 .x1 .x2 31) == some 0x000000006503a9cf
#guard run (.bicRor .x .x0 .x1 .x2 0) == some 0x0123456789abcdef
#guard run (.bicRor .x .x0 .x1 .x2 1) == some 0x000100238081c4e7
#guard run (.bicRor .x .x0 .x1 .x2 63) == some 0x00020047010389ce
#guard run (.bicRor .w .x0 .x1 .x2 0) == some 0x0000000089abcdef
#guard run (.bicRor .w .x0 .x1 .x2 1) == some 0x000000008081c4e7
#guard run (.bicRor .w .x0 .x1 .x2 31) == some 0x00000000010389cf

-- Encodings outside the operand width are rejected, rather than masked.
#guard run (.logicRor .eor .w .x0 .x1 .x2 32) == none
#guard run (.logicRor .eor .x .x0 .x1 .x2 64) == none
#guard run (.bicRor .w .x0 .x1 .x2 32) == none
#guard run (.bicRor .x .x0 .x1 .x2 64) == none

-- Aliased destinations read the old sources before writing the result.
#guard (exec (.logicRor .eor .x .x1 .x1 .x2 1) input).map (·.gpr .x1) ==
  some 0x7e4d182bb281d4e7
#guard (exec (.bicRor .w .x2 .x1 .x2 31) input).map (·.gpr .x2) ==
  some 0x010389cf
#guard (exec (.bicRor .x .x1 .x1 .x1 0) input).map (·.gpr .x1) == some 0
#guard (exec (.logicRor .eor .x .x1 .x1 .x1 0) input).map (·.gpr .x1) == some 0

-- No flags or optional CPU features, and the framework recognizes writes.
#guard (exec (.logicRor .eor .x .x0 .x1 .x2 63) input).map (·.c) == some true
#guard (exec (.bicRor .x .x0 .x1 .x2 63) input).map (·.c) == some true
#guard Instr.requires (.logicRor .eor .x .x0 .x1 .x2 63) == []
#guard Instr.requires (.bicRor .x .x0 .x1 .x2 63) == []
#guard dstOf (.logicRor .eor .x .x0 .x1 .x2 63) == some .x0
#guard dstOf (.bicRor .x .x0 .x1 .x2 63) == some .x0

#guard printer.instr (.logicRor .and .w .x0 .x1 .x2 0) == ["and w0, w1, w2, ror #0"]
#guard printer.instr (.logicRor .orr .x .x0 .x1 .x2 1) == ["orr x0, x1, x2, ror #1"]
#guard printer.instr (.logicRor .eor .x .x0 .x1 .x2 63) == ["eor x0, x1, x2, ror #63"]
#guard printer.instr (.bicRor .w .x0 .x1 .x2 31) == ["bic w0, w1, w2, ror #31"]
#guard printer.instr (.bicRor .x .x0 .x1 .x2 0) == ["bic x0, x1, x2, ror #0"]

-- The result is public exactly when both source operands are public.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.logicRor .eor .x .x0 .x1 .x2 63)).map (AArch64.Taint.pub · .x0)) == some true
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1])
  (.logicRor .eor .x .x0 .x1 .x2 63)).map (AArch64.Taint.pub · .x0)) == some false
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.bicRor .x .x0 .x1 .x2 63)).map (AArch64.Taint.pub · .x0)) == some true
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x2])
  (.bicRor .x .x0 .x1 .x2 63)).map (AArch64.Taint.pub · .x0)) == some false

end VG.Test.AArch64Logical

import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# AArch64 ADC and SBC

Expected results below were produced by the corresponding ADC or SBC
instruction in a Clang inline-assembly probe on an Apple M1 Max (macOS 27),
with the carry set by `cmp` beforehand and read by `cset cs` afterwards (so
the probe also shows that neither instruction writes the carry). The sources
have distinct upper and lower halves, so the 32-bit results check both
truncation of the inputs and zero-extension of the destination. These are
instruction-semantic checks, not cryptographic known-answer vectors.
-/

namespace VG.Test.AArch64Adc
open AArch64

def input (a b : BitVec 64) (carry : Bool) : State where
  gpr r := if r = .x1 then a else if r = .x2 then b else 0xdeadbeefdeadbeef
  sp := 0x1000
  c := carry
  mem _ := 0
  rd := []
  wr := []

def run (i : Instr) (a b : BitVec 64) (carry : Bool) : Option (BitVec 64 × Bool) :=
  (exec i (input a b carry)).map fun s => (s.gpr .x0, s.c)

#guard run (.adc .x .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 false == some (0x0000000000000000, false)
#guard run (.adc .x .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 true == some (0x0000000000000001, true)
#guard run (.adc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 false == some (0x0000000000000003, false)
#guard run (.adc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 true == some (0x0000000000000004, true)
#guard run (.adc .x .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff false == some (0xfffffffffffffffe, false)
#guard run (.adc .x .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff true == some (0xffffffffffffffff, true)
#guard run (.adc .x .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 false == some (0x0000000000000001, false)
#guard run (.adc .x .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 true == some (0x0000000000000002, true)
#guard run (.adc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 false == some (0x0000000000000002, false)
#guard run (.adc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 true == some (0x0000000000000003, true)
#guard run (.adc .x .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 false == some (0x13579bdfffffffff, false)
#guard run (.adc .x .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 true == some (0x13579be000000000, true)
#guard run (.adc .x .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 false == some (0xffffffffffffffff, false)
#guard run (.adc .x .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 true == some (0x0000000000000000, true)
#guard run (.sbc .x .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 false == some (0xfffffffffffffffd, false)
#guard run (.sbc .x .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 true == some (0xfffffffffffffffe, true)
#guard run (.sbc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 false == some (0xfffffffffffffffe, false)
#guard run (.sbc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 true == some (0xffffffffffffffff, true)
#guard run (.sbc .x .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff false == some (0xffffffffffffffff, false)
#guard run (.sbc .x .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff true == some (0x0000000000000000, true)
#guard run (.sbc .x .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 false == some (0xfffffffffffffffe, false)
#guard run (.sbc .x .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 true == some (0xffffffffffffffff, true)
#guard run (.sbc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 false == some (0xffffffffffffffff, false)
#guard run (.sbc .x .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 true == some (0x0000000000000000, true)
#guard run (.sbc .x .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 false == some (0x11111111fffffffe, false)
#guard run (.sbc .x .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 true == some (0x11111111ffffffff, true)
#guard run (.sbc .x .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 false == some (0x02468acf13579bde, false)
#guard run (.sbc .x .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 true == some (0x02468acf13579bdf, true)
#guard run (.adc .w .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 false == some (0x0000000000000000, false)
#guard run (.adc .w .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 true == some (0x0000000000000001, true)
#guard run (.adc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 false == some (0x0000000000000003, false)
#guard run (.adc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 true == some (0x0000000000000004, true)
#guard run (.adc .w .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff false == some (0x00000000fffffffe, false)
#guard run (.adc .w .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff true == some (0x00000000ffffffff, true)
#guard run (.adc .w .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 false == some (0x0000000000000001, false)
#guard run (.adc .w .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 true == some (0x0000000000000002, true)
#guard run (.adc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 false == some (0x0000000000000002, false)
#guard run (.adc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 true == some (0x0000000000000003, true)
#guard run (.adc .w .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 false == some (0x00000000ffffffff, false)
#guard run (.adc .w .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 true == some (0x0000000000000000, true)
#guard run (.adc .w .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 false == some (0x00000000ffffffff, false)
#guard run (.adc .w .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 true == some (0x0000000000000000, true)
#guard run (.sbc .w .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 false == some (0x00000000fffffffd, false)
#guard run (.sbc .w .x0 .x1 .x2) 0xffffffffffffffff 0x0000000000000001 true == some (0x00000000fffffffe, true)
#guard run (.sbc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 false == some (0x00000000fffffffe, false)
#guard run (.sbc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000002 true == some (0x00000000ffffffff, true)
#guard run (.sbc .w .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff false == some (0x00000000ffffffff, false)
#guard run (.sbc .w .x0 .x1 .x2) 0xffffffffffffffff 0xffffffffffffffff true == some (0x0000000000000000, true)
#guard run (.sbc .w .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 false == some (0x00000000fffffffe, false)
#guard run (.sbc .w .x0 .x1 .x2) 0x0000000000000000 0x0000000000000001 true == some (0x00000000ffffffff, true)
#guard run (.sbc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 false == some (0x00000000ffffffff, false)
#guard run (.sbc .w .x0 .x1 .x2) 0x0000000000000001 0x0000000000000001 true == some (0x0000000000000000, true)
#guard run (.sbc .w .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 false == some (0x00000000fffffffe, false)
#guard run (.sbc .w .x0 .x1 .x2) 0x12345678ffffffff 0x0123456700000000 true == some (0x00000000ffffffff, true)
#guard run (.sbc .w .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 false == some (0x0000000013579bde, false)
#guard run (.sbc .w .x0 .x1 .x2) 0x0123456789abcdef 0xfedcba9876543210 true == some (0x0000000013579bdf, true)

-- Aliased destinations read the old sources before writing the result.
#guard (exec (.adc .x .x1 .x1 .x2) (input 1 2 true)).map (·.gpr .x1) == some 4
#guard (exec (.sbc .x .x2 .x1 .x2) (input 1 2 true)).map (·.gpr .x2) == some 0xffffffffffffffff

-- No optional CPU features, and the framework recognizes writes.
#guard Instr.requires (.adc .x .x0 .x1 .x2) == []
#guard Instr.requires (.sbc .x .x0 .x1 .x2) == []
#guard dstOf (.adc .x .x0 .x1 .x2) == some .x0
#guard dstOf (.sbc .x .x0 .x1 .x2) == some .x0

#guard printer.instr (.adc .x .x0 .x1 .x2) == ["adc x0, x1, x2"]
#guard printer.instr (.sbc .w .x0 .x1 .x2) == ["sbc w0, w1, w2"]

-- As for ADCS and SBCS, the untracked carry makes the result secret.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.adc .x .x0 .x1 .x2)).map (AArch64.Taint.pub · .x0)) == some false
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.sbc .x .x0 .x1 .x2)).map (AArch64.Taint.pub · .x0)) == some false

end VG.Test.AArch64Adc

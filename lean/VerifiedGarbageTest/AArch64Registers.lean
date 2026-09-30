import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Axioms

/-!
# Reserved AArch64 registers

The portable target must never encode the platform register x18 or frame
pointer x29 as an ordinary register. In particular, preserving x29 only on
return is insufficient on Apple platforms: it must always address a valid
frame record, including when a leaf function omits its own record.
https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms

Check every constructor against its physical encoding, including x30 after
the gap. This fails if a reserved register is reintroduced or an enum's
position is accidentally used instead of the architectural register number.
-/

namespace VG.Test.AArch64Registers
open AArch64

theorem excludes_reserved (r : Reg) : r.index ≠ 18 ∧ r.index ≠ 29 ∧ r.index < 31 := by
  cases r <;> decide

example : Reg.x28.index = 28 ∧ Reg.x30.index = 30 := by decide

#guard Instr.asm (.addImm .x .x30 .x28 0) == ["add x30, x28, #0"]
#guard Instr.asm (.addImm .w .x30 .x28 0) == ["add w30, w28, #0"]

#assert_standard_axioms excludes_reserved

end VG.Test.AArch64Registers

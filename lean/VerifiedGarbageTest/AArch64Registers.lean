import VerifiedGarbage.TCB.AArch64.Target
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

/-- Every SIMD register has its architectural number, including callee-saved ones. -/
example : (preservedV.map VReg.index) = [8, 9, 10, 11, 12, 13, 14, 15] := by decide

#guard Instr.asm (.vop (.eor3 .v8 .v9 .v10 .v15)) ==
  ["eor3 v8.16b, v9.16b, v10.16b, v15.16b"]
#guard Instr.asm (.ldrq .v12 .x0 16) == ["ldr q12, [x0, #16]"]
#guard Instr.asm (.strq .v15 .x1 0) == ["str q15, [x1, #0]"]

/-- ABI examples test the split at bit 64; they are not cryptographic vectors. -/
def abiState : State := { gpr := fun _ => 0, sp := 0, mem := fun _ => 0, rd := [], wr := [] }

example : abiPreserved abiState (abiState.setV .v8 (1#128 <<< 64)) := by simp [abiPreserved, preservedV, abiState, State.setV]
example : ¬ abiPreserved abiState (abiState.setV .v8 1) := by simp [abiPreserved, preservedV, abiState, State.setV]
example : abiPreserved abiState (abiState.setV .v16 1) := by simp [abiPreserved, preservedV, abiState, State.setV]

/-- Each of the eight low halves is independently protected. -/
example : ∀ r ∈ preservedV, ¬ abiPreserved abiState (abiState.setV r 1) := by
  simp [abiPreserved, preservedV, abiState, State.setV]

#assert_standard_axioms excludes_reserved

end VG.Test.AArch64Registers

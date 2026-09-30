import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.TCB.Axioms

/-! Baseline A64 carry arithmetic: word widths, aliases, carries, borrows,
unsigned multiply-high, flag preservation, and the call boundary. -/

namespace VG.Test.AArch64Carry
open AArch64

private def state (a b : BitVec 64) (carry : Bool) : State where
  gpr r := if r = .x0 then a else if r = .x1 then b else 0
  sp := 0x1000
  c := carry
  mem _ := 0
  rd := []
  wr := []

private def result (i : Instr) (a b : BitVec 64) (carry : Bool) :
    Option (BitVec 64 × Bool) :=
  (exec i (state a b carry)).map fun s => (s.gpr .x0, s.c)

theorem carry64 :
    result (.adds .x .x0 .x0 .x1) 0xffffffffffffffff 1 false = some (0, true) ∧
    result (.adds .x .x0 .x0 .x1) 1 2 true = some (3, false) ∧
    result (.adcs .x .x0 .x0 .x1) 0xffffffffffffffff 0 true = some (0, true) ∧
    result (.adcs .x .x0 .x0 .x1) 0xffffffffffffffff 0xffffffffffffffff true =
      some (0xffffffffffffffff, true) ∧
    result (.adcs .x .x0 .x0 .x1) 1 2 false = some (3, false) := by decide

theorem borrow64 :
    result (.subs .x .x0 .x0 .x1) 0 1 true = some (0xffffffffffffffff, false) ∧
    result (.subs .x .x0 .x0 .x1) 1 1 false = some (0, true) ∧
    result (.sbcs .x .x0 .x0 .x1) 1 1 false = some (0xffffffffffffffff, false) ∧
    result (.sbcs .x .x0 .x0 .x1) 1 1 true = some (0, true) ∧
    result (.sbcs .x .x0 .x0 .x1) 0 0xffffffffffffffff false = some (0, false) := by decide

-- W operands discard the upper halves, and writing W clears the upper half.
theorem word32 :
    result (.adds .w .x0 .x0 .x1) 0x12345678ffffffff 1 false = some (0, true) ∧
    result (.adcs .w .x0 .x0 .x1) 0x12345678ffffffff 0 true = some (0, true) ∧
    result (.subs .w .x0 .x0 .x1) 0x1234567800000000 1 true = some (0xffffffff, false) ∧
    result (.sbcs .w .x0 .x0 .x1) 0x1234567800000001 1 false = some (0xffffffff, false) := by decide

theorem high_product :
    result (.umulh .x0 .x0 .x1) 0xffffffffffffffff 0xffffffffffffffff false =
      some (0xfffffffffffffffe, false) ∧
    result (.umulh .x0 .x0 .x1) 0x8000000000000000 2 true = some (1, true) ∧
    result (.umulh .x0 .x0 .x1) 0xffffffff 0xffffffff false = some (0, false) := by decide

-- Non-flag-setting arithmetic must not destroy a carry between limbs.
theorem carry_preserved :
    result (.add .x .x0 .x0 .x1) 1 1 true = some (2, true) ∧
    result (.sub .x .x0 .x0 .x1) 0 1 false = some (0xffffffffffffffff, false) ∧
    result (.mul .x .x0 .x0 .x1) 2 3 true = some (6, true) := by decide

theorem two_limb_chains :
    ((exec (.adds .x .x0 .x0 .x1) (state 0xffffffffffffffff 1 false)).bind
      (exec (.adcs .x .x2 .x2 .x2))).map (fun s => (s.gpr .x0, s.gpr .x2, s.c)) =
        some (0, 1, false) ∧
    ((exec (.subs .x .x0 .x0 .x1) (state 0 1 true)).bind
      (exec (.sbcs .x .x2 .x2 .x2))).map (fun s => (s.gpr .x0, s.gpr .x2, s.c)) =
        some (0xffffffffffffffff, 0xffffffffffffffff, false) := by decide

theorem veneer_carry (s : State) :
    (call s).map (·.c) = some ((s.unknowns 3).getLsbD 0) := rfl

theorem veneer_unknowns (s : State) (n : Nat) :
    (call s).map (fun t => t.unknowns n) = some (s.unknowns (n + 4)) := rfl

-- Even public source registers do not make an untracked carry public.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x0, .x1]) (.adcs .x .x0 .x0 .x1)).map
  (fun τ => AArch64.Taint.pub τ .x0)) == some false

#guard Instr.asm (.adds .x .x0 .x1 .x2) == ["adds x0, x1, x2"]
#guard Instr.asm (.adcs .w .x0 .x1 .x2) == ["adcs w0, w1, w2"]
#guard Instr.asm (.subs .w .x0 .x1 .x2) == ["subs w0, w1, w2"]
#guard Instr.asm (.sbcs .x .x0 .x1 .x2) == ["sbcs x0, x1, x2"]
#guard Instr.asm (.umulh .x0 .x1 .x2) == ["umulh x0, x1, x2"]

#guard ([Instr.adds .x .x0 .x1 .x2, .adcs .w .x0 .x1 .x2, .subs .w .x0 .x1 .x2,
  .sbcs .x .x0 .x1 .x2, .umulh .x0 .x1 .x2].all (·.requires.isEmpty))

#assert_standard_axioms carry64
#assert_standard_axioms borrow64
#assert_standard_axioms word32
#assert_standard_axioms high_product
#assert_standard_axioms carry_preserved
#assert_standard_axioms two_limb_chains
#assert_standard_axioms veneer_carry
#assert_standard_axioms veneer_unknowns

end VG.Test.AArch64Carry

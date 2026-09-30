import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# ARMv7 call-clobbered flags

AAELF32 2025Q4, section 5.6.1.4 (Call and Jump relocations), permits linker
veneers to corrupt r12 and the condition flags:
https://github.com/ARM-software/abi-aa/blob/2025Q4/aaelf32/aaelf32.rst

A comparison before a call must not determine a branch after it, even when
the callee itself is empty. This witness has a permitted execution returning
zero, so it cannot satisfy a signature-derived contract requiring one.
The old call model instead proved that contract. These are kernel-checked
statements about the model, not hardware or linker execution tests.
-/

namespace VG.Test.ArmCallFlags
open Arm

def code : Prog isa :=
  .seq (.block [.mov .r3 (.reg .lr), .cmp .r0 (.reg .r0)])
    (.seq (.call "review_noop" (.block []))
      (.seq (.ite .eq (.block [.movw .r0 1]) (.block [.movw .r0 0]))
        (.block [.mov .lr (.reg .r3)])))

def initial : State where
  gpr _ := 0
  sp := 4096
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := []

def beforeCall : State := subFlags (initial.setReg .r3 0) 0 0
def afterCall : State :=
  { (beforeCall.setReg .lr 0).setReg .r12 0 with
    n := false, z := false, c := false, v := false }
def finish : State := (afterCall.setReg .r0 0).setReg .lr 0

theorem execution : Exec isa code initial [.branch false] finish := by
  unfold code
  apply Exec.seq (s₂ := beforeCall) (t₁ := [])
  · exact .block rfl
  · apply Exec.seq (s₂ := afterCall) (t₁ := [])
    · apply Exec.call (M := isa) (s₁ := afterCall) (s₂ := afterCall) (t := [])
      · rfl
      · exact .block rfl
      · rfl
    · apply Exec.seq (s₂ := afterCall.setReg .r0 0) (t₁ := [.branch false]) (t₂ := [])
      · exact .iteF rfl (.block rfl)
      · exact .block rfl

def sig : Sig := { params := [], ret := some .u32 }
def contract : Contract isa :=
  sig.contract abi (post := fun m m' r => r = 1 ∧ m' = m)

theorem rejectsBadContract : ¬ Verified target code contract := by
  intro h
  have hp : contract.pre initial := by
    change (4096 : BitVec 32).toNat + 0 ≤ 2 ^ 32 ∧ [] = ([] : List Region) ∧
      [] = ([] : List Region) ∧ List.Pairwise _ [] ∧ (∀ r ∈ ([] : List Region), _) ∧
      (∀ a ∈ ([] : List (Region × Bool)), _) ∧ True
    simp
  obtain ⟨t, s, he, _, hpost⟩ := h.1 initial hp
  obtain ⟨rfl, rfl⟩ := Exec.det he execution
  have impossible : (0 : BitVec 32) = 1 := hpost.1
  exact (by decide : (0 : BitVec 32) ≠ 1) impossible

#assert_standard_axioms execution
#assert_standard_axioms rejectsBadContract
end VG.Test.ArmCallFlags

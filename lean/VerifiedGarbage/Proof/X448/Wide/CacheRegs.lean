import VerifiedGarbage.Impl.X448.AArch64.Cached
import VerifiedGarbage.Proof.X448.Wide.Term

/-! Untrusted: register allocation for cached wide X448 operands. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Cached
open VG.Proof.X448.AArch64 (Keeps)

abbrev termRegs : List Reg := [.x4, .x5, .x10, .x11]

def sqrRegs : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16]

theorem cacheReg_kept {i : Nat} (hi : i < 8) : cacheReg i ∉ ([.x4, .x5, .x10, .x11] : List Reg) := by
  have h : ∀ n < 8, cacheReg n ∉ ([.x4, .x5, .x10, .x11] : List Reg) := by decide +kernel
  exact h i hi

theorem cacheReg_member {i : Nat} (hi : i < 8) : cacheReg i ∈ sqrRegs := by
  have h : ∀ n < 8, cacheReg n ∈ sqrRegs := by decide +kernel
  exact h i hi

theorem cacheReg_ne10 {i : Nat} (hi : i < 8) : cacheReg i ≠ .x10 := by
  intro h
  exact cacheReg_kept hi (by rw [h]; decide)

theorem cacheReg_ne11 {i : Nat} (hi : i < 8) : cacheReg i ≠ .x11 := by
  intro h
  exact cacheReg_kept hi (by rw [h]; decide)

theorem cacheReg_ne3 (i : Nat) : cacheReg i ≠ .x3 := by
  unfold cacheReg
  split <;> decide

theorem cacheReg_inj {i j : Nat} (hi : i < 8) (hj : j < 8) : cacheReg i = cacheReg j ↔ i = j := by
  have h : ∀ i < 8, ∀ j < 8, cacheReg i = cacheReg j ↔ i = j := by decide +kernel
  exact h i hi j hj

end VG.Proof.X448.Wide

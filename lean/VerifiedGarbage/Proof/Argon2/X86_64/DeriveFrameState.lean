import VerifiedGarbage.Proof.Argon2.X86_64.DeriveFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! Exact stack depth and memory modified by the entry-point prologue. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_sp (s : State) (rs : List Reg) :
    (frameStart s rs).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (272 + 8 * rs.length) := by
  induction rs generalizing s with
  | nil => rw [frameStart, pushed_rsp]; rfl
  | cons r rs ih =>
    rw [frameStart, ih, pushed_rsp]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
    exact congrArg (fun n => s.gpr .rsp - BitVec.ofNat 64 n) (by omega)

theorem frameStart_reg (s : State) (rs : List Reg) (r : Reg) (notSp : r ≠ .rsp) :
    (frameStart s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => exact pushed_gpr _ _ notSp
  | cons x xs ih => exact (ih (pushed [x] s)).trans (pushed_gpr _ _ notSp)

theorem frameStart_rd (s : State) (rs : List Reg) : (frameStart s rs).rd = s.rd := by
  induction rs generalizing s with
  | nil => exact pushed_rd ..
  | cons r rs ih => exact (ih (pushed [r] s)).trans (pushed_rd ..)

theorem frameStart_frame (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat) :
    Frame [below (s.gpr .rsp) (272 + 8 * rs.length)] s.mem (frameStart s rs).mem := by
  induction rs generalizing s with
  | nil =>
    exact (pushRegs_mem s (List.replicate 34 .rax) (by decide) (by simpa using space)).1
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega
    have outer := (pushRegs_mem s [r] (by simpa using notSp.1)
      (by simpa using enough)).1
    have inner := ih (pushed [r] s) notSp.2 innerSpace
    apply (outer.sub ?_).trans (inner.sub ?_)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub_below (s.gpr .rsp) (by simp only [List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_singleton, Nat.mul_one]; omega)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [pushed_rsp]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one, below]
      rw [BitVec.sub_sub, ← BitVec.ofNat_add,
        show 8 + (272 + 8 * rs.length) = 272 + 8 * (rs.length + 1) by omega]
      exact Region.sub_prefix (by omega)

theorem frameEnd_mem (s : State) (rs : List Reg) : (frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => exact popped_mem ..
  | cons r rs ih => exact (popped_mem ..).trans ih

theorem frameEnd_rd (s : State) (rs : List Reg) : (frameEnd s rs).rd = s.rd := by
  induction rs with
  | nil => exact popped_rd ..
  | cons r rs ih => exact (popped_rd ..).trans ih

end VG.Proof.Argon2.X86_64.Derive

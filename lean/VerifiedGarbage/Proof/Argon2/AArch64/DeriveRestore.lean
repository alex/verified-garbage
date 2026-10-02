import VerifiedGarbage.Proof.Argon2.AArch64.DeriveSaved
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Reload all saved registers from their unchanged stack slots. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem frameEnd_sp (s : State) (rs : List Reg) :
    (frameEnd s rs).sp = s.sp + BitVec.ofNat 64 (272 + 16 * rs.length) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change (frameEnd s rs).sp + 16 = _
    rw [ih, BitVec.add_assoc, show (16 : Addr) = BitVec.ofNat 64 16 from rfl,
      ← BitVec.ofNat_add]
    exact congrArg (fun n => s.sp + BitVec.ofNat 64 n)
      (by simp only [List.length_cons]; omega)

theorem popped_one_reg (s : State) (r : Reg) :
    (popped r s).gpr r = s.mem.readW s.sp 64 := by
  simp only [popped, RegUpd.gpr_write_self, BitVec.setWidth_eq]
  rfl

theorem frameEnd_restore (s : State) (rs : List Reg) (values : Reg → Addr)
    (distinct : rs.Nodup)
    (words : ∀ j (hj : j < rs.length),
      s.mem.readW (s.sp + BitVec.ofNat 64 (272 + 16 * rs.length - 16 * (j + 1))) 64 = values rs[j]) :
    ∀ r ∈ rs, (frameEnd s rs).gpr r = values r := by
  induction rs with
  | nil => intro r hr; exact False.elim (List.not_mem_nil hr)
  | cons r rs ih =>
    have nodup := List.nodup_cons.mp distinct
    have innerWords : ∀ j (hj : j < rs.length),
        s.mem.readW (s.sp + BitVec.ofNat 64 (272 + 16 * rs.length - 16 * (j + 1))) 64 = values rs[j] := by
      intro j hj
      have word := words (j + 1) (by simp only [List.length_cons]; omega)
      have offset : 272 + 16 * (r :: rs).length - 16 * (j + 1 + 1) =
          272 + 16 * rs.length - 16 * (j + 1) := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    have inner := ih nodup.2 innerWords
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [frameEnd, popped_one_reg, frameEnd_mem, frameEnd_sp]
      have word := words 0 (by simp)
      have offset : 272 + 16 * (x :: rs).length - 16 * (0 + 1) = 272 + 16 * rs.length := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    · change (popped r (frameEnd s rs)).gpr x = _
      have ne : x ≠ r := fun eq => nodup.1 (eq ▸ hx)
      change ((frameEnd s rs).write .x r
        ((frameEnd s rs).mem.readW (frameEnd s rs).sp 64)).gpr x = _
      rw [RegUpd.gpr_write_of_ne _ .x _ ne]
      exact inner x hx

theorem frame_restored (s t : State) (rs : List Reg)
    (distinct : rs.Nodup) (space : 272 + 16 * rs.length ≤ (s.sp).toNat)
    (sp : t.sp = (frameStart s rs).sp)
    (unchanged : ∀ j (_hj : j < rs.length),
      t.mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 =
        (frameStart s rs).mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64) :
    ∀ r ∈ rs, (frameEnd t rs).gpr r = s.gpr r := by
  apply frameEnd_restore t rs s.gpr distinct
  intro j hj
  have offsetBound : 16 * (j + 1) ≤ 272 + 16 * rs.length := by omega
  rw [sp, frameStart_sp, ← Offset.ofNat_sub_ofNat offsetBound, Offset.sub_add_sub_cancel,
    unchanged j hj]
  exact frameStart_word s rs space j hj

theorem frameEnd_reg (s : State) (rs : List Reg) (r : Reg) (other : r ∉ rs) :
    (frameEnd s rs).gpr r = s.gpr r := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at other
    change ((frameEnd s xs).write .x x
      ((frameEnd s xs).mem.readW (frameEnd s xs).sp 64)).gpr r = _
    rw [RegUpd.gpr_write_of_ne _ .x _ other.1, ih other.2]

end VG.Proof.Argon2.AArch64.Derive

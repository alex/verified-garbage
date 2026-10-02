import VerifiedGarbage.Proof.Argon2.X86_64.DeriveSaved
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! Reload all saved registers from their unchanged stack slots. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameEnd_sp (s : State) (rs : List Reg) :
    (frameEnd s rs).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 (120 + 8 * rs.length) := by
  induction rs with
  | nil => rw [frameEnd, popped_rsp]; rfl
  | cons r rs ih =>
    rw [frameEnd, popped_rsp, ih, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    exact congrArg (fun n => s.gpr .rsp + BitVec.ofNat 64 n)
      (by simp only [List.length_cons]; omega)

theorem popped_one_reg (s : State) (r : Reg) (notSp : r ≠ .rsp) :
    (popped r 1 s).gpr r = s.mem.readW (s.gpr .rsp) 64 := by
  change ((s.setReg r (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8)).gpr r = _
  rw [RegUpd.gpr_setReg_of_ne _ _ notSp, RegUpd.gpr_setReg_self]

theorem frameEnd_restore (s : State) (rs : List Reg) (values : Reg → Addr)
    (notSp : .rsp ∉ rs) (distinct : rs.Nodup)
    (words : ∀ j (hj : j < rs.length),
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (120 + 8 * rs.length - 8 * (j + 1))) 64 = values rs[j]) :
    ∀ r ∈ rs, (frameEnd s rs).gpr r = values r := by
  induction rs with
  | nil => intro r hr; exact False.elim (List.not_mem_nil hr)
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have nodup := List.nodup_cons.mp distinct
    have innerWords : ∀ j (hj : j < rs.length),
        s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (120 + 8 * rs.length - 8 * (j + 1))) 64 = values rs[j] := by
      intro j hj
      have word := words (j + 1) (by simp only [List.length_cons]; omega)
      have offset : 120 + 8 * (r :: rs).length - 8 * (j + 1 + 1) =
          120 + 8 * rs.length - 8 * (j + 1) := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    have inner := ih notSp.2 nodup.2 innerWords
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [frameEnd, popped_one_reg _ _ (Ne.symm notSp.1), frameEnd_mem, frameEnd_sp]
      have word := words 0 (by simp)
      have offset : 120 + 8 * (x :: rs).length - 8 * (0 + 1) = 120 + 8 * rs.length := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    · rw [frameEnd, popped_gpr r 1 (frameEnd s rs) (r' := x) (fun h => notSp.2 (h ▸ hx))
        (fun h => nodup.1 (h ▸ hx))]
      exact inner x hx

theorem frame_restored (s t : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (distinct : rs.Nodup) (space : 120 + 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (sp : t.gpr .rsp = (frameStart s rs).gpr .rsp)
    (unchanged : ∀ j (_hj : j < rs.length),
      t.mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
        (frameStart s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64) :
    ∀ r ∈ rs, (frameEnd t rs).gpr r = s.gpr r := by
  apply frameEnd_restore t rs s.gpr notSp distinct
  intro j hj
  have offsetBound : 8 * (j + 1) ≤ 120 + 8 * rs.length := by omega
  rw [sp, frameStart_sp, ← Offset.ofNat_sub_ofNat offsetBound, Offset.sub_add_sub_cancel,
    unchanged j hj]
  exact frameStart_word s rs notSp space j hj

end VG.Proof.Argon2.X86_64.Derive

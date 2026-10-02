import VerifiedGarbage.Proof.Argon2.X86_64.DeriveFrameState

/-! The nested prologue stores every callee-saved register at its exact ABI slot. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_word (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat) (j : Nat) (bound : j < rs.length) :
    (frameStart s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega
    cases j with
    | zero =>
      have stored := (pushRegs_mem s [r] (by simpa using notSp.1)
        (by simpa using enough)).2 0 (by simp)
      have inner := frameStart_frame (pushed [r] s) rs notSp.2 innerSpace
      have unchanged : (frameStart (pushed [r] s) rs).mem.readW ((pushed [r] s).gpr .rsp) 64 =
          (pushed [r] s).mem.readW ((pushed [r] s).gpr .rsp) 64 := inner.readW
        (r := ⟨(pushed [r] s).gpr .rsp, 8⟩) (Region.contains_self _ _) (by
          intro region hr
          simp only [List.mem_singleton] at hr; subst region
          apply Offset.base_disjoint_below
          have limit := (s.gpr .rsp).isLt
          simp only [List.length_cons] at space; omega) (by decide)
      rw [pushed_rsp] at unchanged
      simp only [List.length_singleton, Nat.mul_one] at unchanged
      exact unchanged.trans stored
    | succ j =>
      have word := ih (pushed [r] s) notSp.2 innerSpace j (by simpa using bound)
      rw [pushed_rsp, pushed_gpr _ _ (fun h => notSp.2 (h ▸ List.getElem_mem _))] at word
      simp only [List.length_singleton, Nat.mul_one] at word
      rw [BitVec.sub_sub, ← BitVec.ofNat_add,
        show 8 + 8 * (j + 1) = 8 * (j + 1 + 1) by omega] at word
      exact word

end VG.Proof.Argon2.X86_64.Derive

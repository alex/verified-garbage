import VerifiedGarbage.Proof.Argon2.AArch64.DeriveFrameState

/-! Each saved register occupies the low eight bytes of its 16-byte slot. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem frameStart_word (s : State) (rs : List Reg)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat) (j : Nat) (bound : j < rs.length) :
    (frameStart s rs).mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons r rs ih =>
    have enough : 16 ≤ s.sp.toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      change 272 + 16 * rs.length ≤ (s.sp - 16).toNat
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact enough)]
      change 272 + 16 * rs.length ≤ s.sp.toNat - 16
      simp only [List.length_cons] at space; omega
    cases j with
    | zero =>
      have inner := frameStart_frame (pushed r s) rs innerSpace
      have unchanged : (frameStart (pushed r s) rs).mem.readW (pushed r s).sp 64 =
          (pushed r s).mem.readW (pushed r s).sp 64 := inner.readW
        (r := ⟨(pushed r s).sp, 8⟩) (Region.contains_self _ _) (by
          intro region hr
          simp only [List.mem_singleton] at hr; subst region
          apply Offset.base_disjoint_below
          have limit := s.sp.isLt
          simp only [List.length_cons] at space; omega) (by decide)
      change (frameStart (pushed r s) rs).mem.readW (s.sp - 16) 64 = s.gpr r
      change (frameStart (pushed r s) rs).mem.readW (s.sp - 16) 64 =
        (pushed r s).mem.readW (s.sp - 16) 64 at unchanged
      rw [unchanged]
      exact Mem.readW_writeW_self64 ..
    | succ j =>
      have jBound : j < rs.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using bound
      have word := ih (pushed r s) innerSpace j (by simpa using bound)
      change (frameStart (pushed r s) rs).mem.readW
        (s.sp - 16 - BitVec.ofNat 64 (16 * (j + 1))) 64 = s.gpr rs[j] at word
      rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
        show 16 + 16 * (j + 1) = 16 * (j + 1 + 1) by omega] at word
      exact word
end VG.Proof.Argon2.AArch64.Derive

import VerifiedGarbage.Proof.Argon2.AArch64.DeriveFrame

/-! Merged from `Proof.Argon2.AArch64.DeriveFrameState`. -/
section
/-! Exact stack depth and memory modified by the entry-point prologue. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem frameStart_sp (s : State) (rs : List Reg) :
    (frameStart s rs).sp = s.sp - BitVec.ofNat 64 (272 + 16 * rs.length) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [frameStart, ih]
    change s.sp - 16 - BitVec.ofNat 64 (272 + 16 * rs.length) = _
    rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => s.sp - BitVec.ofNat 64 n) (by simp only [List.length_cons]; omega)

theorem frameStart_reg (s : State) (rs : List Reg) (r : Reg) :
    (frameStart s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (pushed x s)

theorem frameStart_rd (s : State) (rs : List Reg) : (frameStart s rs).rd = s.rd := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih (pushed r s)

theorem frameStart_frame (s : State) (rs : List Reg)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat) :
    Frame [below s.sp (272 + 16 * rs.length)] s.mem (frameStart s rs).mem := by
  induction rs generalizing s with
  | nil => exact Frame.refl _ _
  | cons r rs ih =>
    have enough : 16 ≤ s.sp.toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      change 272 + 16 * rs.length ≤ (s.sp - 16).toNat
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact enough)]
      change 272 + 16 * rs.length ≤ s.sp.toNat - 16
      simp only [List.length_cons] at space; omega
    have outer : Frame [below s.sp 16] s.mem (pushed r s).mem := by
      change Frame [⟨s.sp - 16, 16⟩] s.mem (s.mem.writeW (s.sp - 16) (s.gpr r))
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (by simpa only [BitVec.add_zero] using
          Offset.contains_base (s.sp - 16) (d := 0) (n := 8) (k := 16) (by decide) (by decide))
    have inner := ih (pushed r s) innerSpace
    apply (outer.sub ?_).trans (inner.sub ?_)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons]; omega) (by
        have := s.sp.isLt; omega)⟩
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      change Region.Sub ⟨s.sp - 16 - BitVec.ofNat 64 (272 + 16 * rs.length), 272 + 16 * rs.length⟩
        (below s.sp (272 + 16 * (r :: rs).length))
      simp only [List.length_cons, below]
      rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
        show 16 + (272 + 16 * rs.length) = 272 + 16 * (rs.length + 1) by omega]
      exact Region.sub_prefix (by omega)

theorem frameEnd_mem (s : State) (rs : List Reg) : (frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih

theorem frameEnd_rd (s : State) (rs : List Reg) : (frameEnd s rs).rd = s.rd := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih
end VG.Proof.Argon2.AArch64.Derive
end

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

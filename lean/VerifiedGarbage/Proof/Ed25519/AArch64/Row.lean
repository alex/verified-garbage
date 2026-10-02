import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-! One row of a four-by-four word multiplication. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- One loaded operand and a multiply-accumulate step. -/
theorem mulLoad_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0)
    {d : Nat} (ha : d % 8 = 0) (hd : d + 8 ≤ workSize large) {t : Reg}
    (ht8 : t ≠ .x8) (ht2 : t ≠ .x2) (ht10 : t ≠ .x10)
    (ht20 : t ≠ .x20) (ht9 : t ≠ .x9) :
    WP isa (.block (([ld .x9 d] : List Instr) ++ mulStep t .x20 .x3 .x9)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr .x20).toNat =
        (s.gpr t).toNat + (s.gpr .x20).toNat + (s.gpr .x3).toNat * (word s.mem base d).toNat ∧
      Keeps [t, .x20, .x8, .x2, .x9] s s' := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs ha hd .x9) fun s₁ ⟨v1, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  refine WP.mono (mulStep_ok s₁ hz1 ht8 ht2 ht10 (by decide) (by decide)
    (by decide) (by decide) ht20) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, ?_⟩
  · rw [v1, k1.gpr t (by simpa only [List.mem_singleton] using ht9),
      k1.gpr .x20 (by decide), k1.gpr .x3 (by decide)] at e2
    exact e2
  · have h1 : Keeps [t, .x20, .x8, .x2, .x9] s s₁ := k1.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp)
    have h2 : Keeps [t, .x20, .x8, .x2, .x9] s₁ s₂ := k2.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
    exact h1.trans h2

def rowR (a b i : Nat) (r0 r1 r2 r3 r4 : Reg) : List Instr :=
  ([ld .x3 (a + 8 * i), .movz .w .x20 0 0] : List Instr) ++
    ((([ld .x9 (b + 8 * 0)] : List Instr) ++ mulStep r0 .x20 .x3 .x9) ++
      ((([ld .x9 (b + 8 * 1)] : List Instr) ++ mulStep r1 .x20 .x3 .x9) ++
        ((([ld .x9 (b + 8 * 2)] : List Instr) ++ mulStep r2 .x20 .x3 .x9) ++
          ((([ld .x9 (b + 8 * 3)] : List Instr) ++ mulStep r3 .x20 .x3 .x9) ++ [mov r4 .x20]))))

theorem row_eq (a b i : Nat) :
    row a b i = rowR a b i (wordReg i) (wordReg (i + 1)) (wordReg (i + 2))
      (wordReg (i + 3)) (wordReg (i + 4)) := by
  simp only [row, rowR, List.append_assoc]
  rfl

theorem rowStart_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ workSize large) :
    WP isa (.block [ld .x3 d, .movz .w .x20 0 0]) s fun t =>
      t.gpr .x3 = word s.mem base d ∧ t.gpr .x20 = 0 ∧ Keeps [.x3, .x20] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  apply WP.of_runBlock
  rw [runBlock_cons, load_sc hs ha hd, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec, show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · rw [RegUpd.gpr_write_self]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

/-- A row: `r0 + 2⁶⁴ r1 + 2¹²⁸ r2 + 2¹⁹² r3 + a_i · b`, into `r0`–`r4`. -/
theorem rowR_ok {s : State} {base : Addr} (hs : Scr s base large) {a b i : Nat}
    (ha : a + 8 * i + 8 ≤ workSize large) (hb : b + 32 ≤ workSize large)
    (haa : a % 8 = 0) (hba : b % 8 = 0) (hz : s.gpr .x10 = 0) {r0 r1 r2 r3 r4 : Reg}
    (hd : ([r0, r1, r2, r3, r4, .x8, .x2, .x3, .x20, .x0, .x9, .x10] : List Reg).Nodup) :
    WP isa (.block (rowR a b i r0 r1 r2 r3 r4)) s fun s' =>
      val4 (s'.gpr r0) (s'.gpr r1) (s'.gpr r2) (s'.gpr r3) + 2 ^ 256 * (s'.gpr r4).toNat =
        val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) +
          (word s.mem base (a + 8 * i)).toNat * fe s.mem base b ∧
      Keeps [r0, r1, r2, r3, r4, .x8, .x2, .x3, .x20, .x9] s s' := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h0a, h0d, h0c, h0b, h0i, h09, h0z⟩, ⟨h12, h13, h14, h1a, h1d, h1c, h1b, h1i, h19, h1z⟩,
    ⟨h23, h24, h2a, h2d, h2c, h2b, h2i, h29, h2z⟩, ⟨h34, h3a, h3d, h3c, h3b, h3i, h39, h3z⟩,
    ⟨h4a, h4d, h4c, h4b, h4i, h49, h4z⟩, -⟩ := hd
  rw [rowR, WP.block_append_iff]
  refine WP.mono (rowStart_ok hs (by omega) (by omega)) fun s₁ ⟨c1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (mulLoad_ok hs₁ hz1 (by omega) (by omega) h0a h0d h0z h0b h09) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by simp [Ne.symm h0i])
  have hz2 := (k2.gpr .x10 (by simp [Ne.symm h0z])).trans hz1
  rw [WP.block_append_iff]
  refine WP.mono (mulLoad_ok hs₂ hz2 (by omega) (by omega) h1a h1d h1z h1b h19) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by simp [Ne.symm h1i])
  have hz3 := (k3.gpr .x10 (by simp [Ne.symm h1z])).trans hz2
  rw [WP.block_append_iff]
  refine WP.mono (mulLoad_ok hs₃ hz3 (by omega) (by omega) h2a h2d h2z h2b h29) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by simp [Ne.symm h2i])
  have hz4 := (k4.gpr .x10 (by simp [Ne.symm h2z])).trans hz3
  rw [WP.block_append_iff]
  refine WP.mono (mulLoad_ok hs₄ hz4 (by omega) (by omega) h3a h3d h3z h3b h39) fun s₅ ⟨e5, k5⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, mov, read_x, show (0 : Nat) < 4096 from by decide, ite_true,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  -- The memory and the registers along the way.
  have M1 : s₁.mem = s.mem := k1.mem
  have M2 : s₂.mem = s.mem := k2.mem.trans M1
  have M3 : s₃.mem = s.mem := k3.mem.trans M2
  have M4 : s₄.mem = s.mem := k4.mem.trans M3
  have C2 : s₂.gpr .x3 = s₁.gpr .x3 := k2.gpr _ (by simp [Ne.symm h0c])
  have C3 : s₃.gpr .x3 = s₁.gpr .x3 := (k3.gpr _ (by simp [Ne.symm h1c])).trans C2
  have C4 : s₄.gpr .x3 = s₁.gpr .x3 := (k4.gpr _ (by simp [Ne.symm h2c])).trans C3
  have r0_1 : s₁.gpr r0 = s.gpr r0 := k1.gpr _ (by simp [h0c, h0b])
  have r0_5 : s₅.gpr r0 = s₂.gpr r0 := by
    rw [k5.gpr _ (by simp [h03, h0b, h0a, h0d, h09]), k4.gpr _ (by simp [h02, h0b, h0a, h0d, h09]),
      k3.gpr _ (by simp [h01, h0b, h0a, h0d, h09])]
  have r1_2 : s₂.gpr r1 = s.gpr r1 := by
    rw [k2.gpr _ (by simp [Ne.symm h01, h1b, h1a, h1d, h19]), k1.gpr _ (by simp [h1c, h1b])]
  have r1_5 : s₅.gpr r1 = s₃.gpr r1 := by
    rw [k5.gpr _ (by simp [h13, h1b, h1a, h1d, h19]), k4.gpr _ (by simp [h12, h1b, h1a, h1d, h19])]
  have r2_3 : s₃.gpr r2 = s.gpr r2 := by
    rw [k3.gpr _ (by simp [Ne.symm h12, h2b, h2a, h2d, h29]), k2.gpr _ (by simp [Ne.symm h02, h2b, h2a, h2d, h29]),
      k1.gpr _ (by simp [h2c, h2b])]
  have r2_5 : s₅.gpr r2 = s₄.gpr r2 := k5.gpr _ (by simp [h23, h2b, h2a, h2d, h29])
  have r3_4 : s₄.gpr r3 = s.gpr r3 := by
    rw [k4.gpr _ (by simp [Ne.symm h23, h3b, h3a, h3d, h39]), k3.gpr _ (by simp [Ne.symm h13, h3b, h3a, h3d, h39]),
      k2.gpr _ (by simp [Ne.symm h03, h3b, h3a, h3d, h39]), k1.gpr _ (by simp [h3c, h3b])]
  refine ⟨?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [M1, M2, M3, M4, C2, C3, C4, c1, b1, r0_1, r1_2, r2_3, r3_4, z, Nat.mul_zero,
      Nat.add_zero, Nat.mul_one, Nat.reduceMul, word] at e2 e3 e4 e5
    simp only [val4, fe, word, RegUpd.gpr_write_of_ne _ _ _ h04, RegUpd.gpr_write_of_ne _ _ _ h14,
      RegUpd.gpr_write_of_ne _ _ _ h24, RegUpd.gpr_write_of_ne _ _ _ h34, r0_5, r1_5, r2_5]
    have hp : ∀ x y z w v : Nat, v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
        v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by
      intro x y z w v
      simp only [Nat.mul_add, Nat.mul_left_comm v]
    rw [hp]
    omega_using [e2, e3, e4, e5]
  · have h9 : r ≠ .x9 := fun he => hr (by simp [he])
    have hrOld : r ∉ [r0, r1, r2, r3, r4, .x8, .x2, .x3, .x20] :=
      fun hm => hr (List.mem_append_left _ hm)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrOld
    rw [RegUpd.gpr_write_of_ne _ _ _ hrOld.2.2.2.2.1]
    rw [k5.gpr _ (by simp [hrOld.2.2.2.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k4.gpr _ (by simp [hrOld.2.2.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k3.gpr _ (by simp [hrOld.2.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k2.gpr _ (by simp [hrOld.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k1.gpr _ (by simp [hrOld.2.2.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.2.2])]
  · exact k5.mem.trans M4
  · rw [RegUpd.rd_write, k5.rd, k4.rd, k3.rd, k2.rd, k1.rd]
  · rw [RegUpd.wr_write, k5.wr, k4.wr, k3.wr, k2.wr, k1.wr]

  · rw [RegUpd.sp_write, k5.sp, k4.sp, k3.sp, k2.sp, k1.sp]

end VG.Proof.Ed25519.AArch64

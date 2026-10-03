import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed25519.AArch64.Ops
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! Merged from `Proof.Ed25519.AArch64.Row`. -/
section
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
end

/-! Merged from `Proof.Ed25519.AArch64.Reduce`. -/
section
/-! Reduction of an eight-word field product. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem fold_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hb : (s.gpr .x20).toNat < 2 ^ 52) :
    WP isa (.block fold) s fun t =>
      toFe (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 38 * (s.gpr .x20).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mul .x .x8 .x20 .x11]) s fun t =>
      (t.gpr .x8).toNat = 38 * (s.gpr .x20).toNat ∧ Keeps [.x8] s t from by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', h38]
    refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [BitVec.toNat_mul, show (38 : Word).toNat = 38 from rfl, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    · intro r hr
      exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr))
    fun s₁ ⟨e1, k1⟩ => ?_
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  have h381 := (k1.gpr .x11 (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by rw [e1]; omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans k2⟩
  rw [e2, e1, k1.gpr .x4 (by decide), k1.gpr .x5 (by decide),
    k1.gpr .x6 (by decide), k1.gpr .x7 (by decide)]

/-- The eight words of a full product: x4–x7, then x21–x24. -/
abbrev wide (s : State) : Nat :=
  val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
    2 ^ 256 * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem movz38_ok (s : State) :
    WP isa (.block [.movz .w .x11 38 0]) s fun t => t.gpr .x11 = 38 ∧ Keeps [.x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)

/-- `reduceWide`: the eight words of a product, reduced modulo p into x4–x7. -/
theorem reduceWide_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block reduceWide) s fun t =>
      toFe (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) = toFe (wide s) ∧
      t.gpr .x10 = 0 ∧
      Keeps [.x2, .x8, .x9, .x11, .x16, .x4, .x5, .x6, .x7, .x20] s t := by
  rw [reduceWide, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movz38_ok s) fun s₁ ⟨h38, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (rowAccReduce_ok s₁ hz1) fun s₂ ⟨e2, k2⟩ => ?_
  have hz2 : s₂.gpr .x10 = 0 := (k2.gpr _ (by decide)).trans hz1
  have h382 : s₂.gpr .x11 = 38 := (k2.gpr _ (by decide)).trans h38
  have hc : (s₂.gpr .x20).toNat < 2 ^ 52 := by
    have hl := val4_lt (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7)
    have hh := val4_lt (s₁.gpr .x21) (s₁.gpr .x22) (s₁.gpr .x23) (s₁.gpr .x24)
    rw [h38, show (38 : Word).toNat = 38 from rfl] at e2
    omega_using [e2, hl, hh]
  refine WP.mono (fold_ok s₂ hz2 h382 hc) fun s₃ ⟨e3, k3⟩ => ?_
  refine ⟨?_, (k3.gpr _ (by decide)).trans hz2,
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  rw [e3]
  rw [h38, show (38 : Word).toNat = 38 from rfl, k1.gpr .x4 (by decide), k1.gpr .x5 (by decide),
    k1.gpr .x6 (by decide), k1.gpr .x7 (by decide), k1.gpr .x21 (by decide),
    k1.gpr .x22 (by decide), k1.gpr .x23 (by decide), k1.gpr .x24 (by decide)] at e2
  apply toFe_congr
  rw [← fold256, e2, fold256]

end VG.Proof.Ed25519.AArch64
end

/-! Four-by-four word field multiplication and its memory frame. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem row0 (a b : Nat) : row a b 0 = rowR a b 0 .x4 .x5 .x6 .x7 .x21 := row_eq a b 0
theorem row1 (a b : Nat) : row a b 1 = rowR a b 1 .x5 .x6 .x7 .x21 .x22 := row_eq a b 1
theorem row2 (a b : Nat) : row a b 2 = rowR a b 2 .x6 .x7 .x21 .x22 .x23 := row_eq a b 2
theorem row3 (a b : Nat) : row a b 3 = rowR a b 3 .x7 .x21 .x22 .x23 .x24 := row_eq a b 3

theorem fe_mul_expand (m : Mem) (base : Addr) (a B : Nat) :
    fe m base a * B = (word m base (a + 8 * 0)).toNat * B + 2 ^ 64 * ((word m base (a + 8 * 1)).toNat * B) +
      2 ^ 128 * ((word m base (a + 8 * 2)).toNat * B) + 2 ^ 192 * ((word m base (a + 8 * 3)).toNat * B) := by
  simp only [fe, val4, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul,
    Nat.add_mul, Nat.mul_assoc]

def wideClob : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x20, .x21, .x22, .x23, .x24]

theorem rowsAccumulate_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) :
    WP isa (.block (row a b 0 ++ (row a b 1 ++ (row a b 2 ++ row a b 3)))) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) +
        2 ^ 256 * val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
            fe s.mem base a * fe s.mem base b ∧ Keeps wideClob s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨haa, ha⟩ := ha
  obtain ⟨hba, hb⟩ := hb
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.gpr r h
  rw [WP.block_append_iff, row0]
  refine WP.mono (rowR_ok hs (by omega) hb haa hba hz (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 := (g k1 .x10 (by decide)).trans hz
  rw [WP.block_append_iff, row1]
  refine WP.mono (rowR_ok hs₁ (by omega) hb haa hba hz1 (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hz2 := (g k2 .x10 (by decide)).trans hz1
  rw [WP.block_append_iff, row2]
  refine WP.mono (rowR_ok hs₂ (by omega) hb haa hba hz2 (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  have hz3 := (g k3 .x10 (by decide)).trans hz2
  rw [row3]
  refine WP.mono (rowR_ok hs₃ (by omega) hb haa hba hz3 (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have K : Keeps wideClob s s₄ :=
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans
      (k3.mono (by decide)) |>.trans (k4.mono (by decide))
  refine ⟨?_, K⟩
  rw [fe_mul_expand]
  rw [k1.mem] at e2
  rw [k2.mem, k1.mem] at e3
  rw [k3.mem, k2.mem, k1.mem] at e4
  have r1 := g k2 .x4 (by decide)
  have r2 := g k3 .x4 (by decide)
  have r3 := g k4 .x4 (by decide)
  have q2 := g k3 .x5 (by decide)
  have q3 := g k4 .x5 (by decide)
  have q4 := g k4 .x6 (by decide)
  simp only [val4] at e1 e2 e3 e4 ⊢
  rw [r3, r2, r1, q3, q2, q4]
  omega_using [e1, e2, e3, e4]

/-- Rows 1–3 and the loads keep the words of `b` (x12–x15), x4 and x10. -/
def mulRowClob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24]

theorem fe_mul_expand4 (A0 A1 A2 A3 B : Nat) :
    (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) * B =
      A0 * B + 2 ^ 64 * (A1 * B) + 2 ^ 128 * (A2 * B) + 2 ^ 192 * (A3 * B) := by
  simp only [Nat.add_mul, Nat.mul_assoc]

theorem mulWide_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) :
    WP isa (.block (mulWide a b)) s fun t =>
      wide t = fe s.mem base a * fe s.mem base b ∧
      Keeps (.x12 :: .x13 :: .x14 :: .x15 :: mulRowClob) s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨haa, ha'⟩ := ha
  simp only [mulWide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs ⟨hb.1, hb.2⟩ (by decide)) fun s₁ ⟨b0, b1, b2, b3, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₁ (by omega) (by omega) .x3) fun s₂ ⟨a0, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowFirst_ok s₂ ((k2.gpr _ (by decide)).trans hz1)) fun s₃ ⟨e0, k3⟩ => ?_
  have K3 : Keeps mulRowClob s₁ s₃ := (k2.mono (by decide)).trans (k3.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K3 (by decide)) (by omega) (by omega) .x3)
    fun s₄ ⟨a1, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowAcc1_ok s₄ ((K3.trans (k4.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₅ ⟨e1, k5⟩ => ?_
  have K5 : Keeps mulRowClob s₁ s₅ := (K3.trans (k4.mono (by decide))).trans (k5.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K5 (by decide)) (by omega) (by omega) .x3)
    fun s₆ ⟨a2, k6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowAcc2_ok s₆ ((K5.trans (k6.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₇ ⟨e2, k7⟩ => ?_
  have K7 : Keeps mulRowClob s₁ s₇ := (K5.trans (k6.mono (by decide))).trans (k7.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K7 (by decide)) (by omega) (by omega) .x3)
    fun s₈ ⟨a3, k8⟩ => ?_
  refine WP.mono (rowAcc3_ok s₈ ((K7.trans (k8.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₉ ⟨e3, k9⟩ => ?_
  have K9 : Keeps mulRowClob s₁ s₉ := (K7.trans (k8.mono (by decide))).trans (k9.mono (by decide))
  refine ⟨?_, (k1.mono (by decide)).trans (K9.mono (by decide))⟩
  -- The words of `a` and `b` at each row, and where each word of the result was last written.
  have B : ∀ (t : State), Keeps mulRowClob s₁ t →
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) = fe s.mem base b := by
    intro t k
    rw [k.gpr .x12 (by decide), k.gpr .x13 (by decide), k.gpr .x14 (by decide),
      k.gpr .x15 (by decide), b0, b1, b2, b3]
  rw [B s₂ (k2.mono (by decide)), a0, k1.mem] at e0
  rw [B s₄ (K3.trans (k4.mono (by decide))), a1, K3.mem, k1.mem, k4.gpr .x5 (by decide),
    k4.gpr .x6 (by decide), k4.gpr .x7 (by decide), k4.gpr .x21 (by decide)] at e1
  rw [B s₆ (K5.trans (k6.mono (by decide))), a2, K5.mem, k1.mem, k6.gpr .x6 (by decide),
    k6.gpr .x7 (by decide), k6.gpr .x21 (by decide), k6.gpr .x22 (by decide)] at e2
  rw [B s₈ (K7.trans (k8.mono (by decide))), a3, K7.mem, k1.mem, k8.gpr .x7 (by decide),
    k8.gpr .x21 (by decide), k8.gpr .x22 (by decide), k8.gpr .x23 (by decide)] at e3
  have K39 : Keeps [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₃ s₉ :=
    (((((k4.mono (by decide)).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))
  have K59 : Keeps [.x2, .x3, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₅ s₉ :=
    (((k6.mono (by decide)).trans (k7.mono (by decide))).trans (k8.mono (by decide))).trans
      (k9.mono (by decide))
  have K79 : Keeps [.x2, .x3, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₇ s₉ :=
    (k8.mono (by decide)).trans (k9.mono (by decide))
  have hf : fe s.mem base a * fe s.mem base b =
      (word s.mem base a).toNat * fe s.mem base b +
        2 ^ 64 * ((word s.mem base (a + 8)).toNat * fe s.mem base b) +
        2 ^ 128 * ((word s.mem base (a + 16)).toNat * fe s.mem base b) +
        2 ^ 192 * ((word s.mem base (a + 24)).toNat * fe s.mem base b) :=
    fe_mul_expand4 _ _ _ _ _
  dsimp only [wide]
  rw [hf, K39.gpr .x4 (by decide), K59.gpr .x5 (by decide), K79.gpr .x6 (by decide)]
  generalize fe s.mem base b = FB at e0 e1 e2 e3 ⊢
  simp only [val4] at e0 e1 e2 e3 ⊢
  omega_using [e0, e1, e2, e3]

theorem zeroReg_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .w r 0 0]) s fun t => t.gpr r = 0 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)

/-- Reduce the eight words of a product and store the result at `o`. -/
theorem fieldFinish_ok {s₀ s : State} {base : Addr} (hs : Scr s base large) {o : Nat}
    (ho : FieldRange o large) (hz : s.gpr .x10 = 0) (k : Keeps clob s₀ s) :
    WP isa (.block (reduceWide ++ store4 o)) s fun t =>
      Op base o s₀ t ∧ F t.mem base o = toFe (wide s) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [WP.block_append_iff]
  refine WP.mono (reduceWide_ok s hz) fun s₁ ⟨e1, _, k1⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps k1 (by decide)) ho) fun s₂ heq => ?_
  subst s₂
  refine ⟨Op.of_store ho (k.trans (k1.mono (by decide))) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega)]
  exact e1

/-- Multiplication modulo p, allowing the output to alias either input. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldMul o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldMul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulWide_ok hs₀ ha hb hz) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (fieldFinish_ok (hs₀.of_keeps k1 (by decide)) ho
    ((k1.gpr _ (by decide)).trans hz) ((k0.mono (by decide)).trans (k1.mono (by decide))))
    fun t ⟨hop, ht⟩ => ⟨hop, ?_⟩
  rw [ht, e1, k0.mem]
  exact toFe_mul rfl

end VG.Proof.Ed25519.AArch64

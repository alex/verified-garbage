import VerifiedGarbage.Proof.X25519.X86_64.Mem
import Mathlib.Tactic.Ring

/-!
# X25519 on x86-64: multiplication

A row of the product (`row`), for any five registers, from four
multiply-accumulate steps (`mulStep_ok`); the reduction of the eight-word
product (`reduce`); and the multiplication `mul o a b`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- A row of a product, into the registers `r0`–`r4`. -/
def rowR (a b i : Nat) (r0 r1 r2 r3 r4 : Reg) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8 * i))), .mov32 .rbp (.imm 0)] ++
    (mulStep r0 .rbp .rcx (.mem (sc (b + 8 * 0))) ++ (mulStep r1 .rbp .rcx (.mem (sc (b + 8 * 1))) ++
      (mulStep r2 .rbp .rcx (.mem (sc (b + 8 * 2))) ++ (mulStep r3 .rbp .rcx (.mem (sc (b + 8 * 3))) ++
        [.mov r4 (.reg .rbp)]))))

theorem row_eq (a b i : Nat) :
    row a b i = rowR a b i (t i) (t (i + 1)) (t (i + 2)) (t (i + 3)) (t (i + 4)) := by
  simp only [row, rowR, List.append_assoc]
  rfl

/-- The start of a row: `rcx = a_i`, `rbp = 0`. -/
theorem rowStart_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    WP isa (.block [.mov .rcx (.mem (sc d)), .mov32 .rbp (.imm 0)]) s fun s' =>
      s'.gpr .rcx = word s.mem base d ∧ s'.gpr .rbp = 0 ∧ Keeps [.rcx, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, readSrc32,
    Option.map_some, State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-- A row: `r0 + 2⁶⁴ r1 + 2¹²⁸ r2 + 2¹⁹² r3 + a_i · b`, into `r0`–`r4`. -/
theorem rowR_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : a + 8 * i + 8 ≤ 4096) (hb : b + 32 ≤ 4096) {r0 r1 r2 r3 r4 : Reg}
    (hd : ([r0, r1, r2, r3, r4, .rax, .rdx, .rcx, .rbp, .rdi] : List Reg).Nodup) :
    WP isa (.block (rowR a b i r0 r1 r2 r3 r4)) s fun s' =>
      val4 (s'.gpr r0) (s'.gpr r1) (s'.gpr r2) (s'.gpr r3) + 2 ^ 256 * (s'.gpr r4).toNat =
        val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) +
          (word s.mem base (a + 8 * i)).toNat * fe s.mem base b ∧
      Keeps [r0, r1, r2, r3, r4, .rax, .rdx, .rcx, .rbp] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h0a, h0d, h0c, h0b, h0i⟩, ⟨h12, h13, h14, h1a, h1d, h1c, h1b, h1i⟩,
    ⟨h23, h24, h2a, h2d, h2c, h2b, h2i⟩, ⟨h34, h3a, h3d, h3c, h3b, h3i⟩,
    ⟨h4a, h4d, h4c, h4b, h4i⟩, -⟩ := hd
  rw [rowR, WP.block_append_iff]
  refine WP.mono (rowStart_ok hs (by omega)) fun s₁ ⟨c1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₁ (readSrc_sc hs₁ (by omega)) h0a h0d (by decide) (by decide)
    (by decide) h0b) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by simp [Ne.symm h0i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₂ (readSrc_sc hs₂ (by omega)) h1a h1d (by decide) (by decide)
    (by decide) h1b) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by simp [Ne.symm h1i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₃ (readSrc_sc hs₃ (by omega)) h2a h2d (by decide) (by decide)
    (by decide) h2b) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by simp [Ne.symm h2i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₄ (readSrc_sc hs₄ (by omega)) h3a h3d (by decide) (by decide)
    (by decide) h3b) fun s₅ ⟨e5, k5⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  -- The memory and the registers along the way.
  have M1 : s₁.mem = s.mem := k1.2.1
  have M2 : s₂.mem = s.mem := k2.2.1.trans M1
  have M3 : s₃.mem = s.mem := k3.2.1.trans M2
  have M4 : s₄.mem = s.mem := k4.2.1.trans M3
  have C2 : s₂.gpr .rcx = s₁.gpr .rcx := k2.1 _ (by simp [Ne.symm h0c])
  have C3 : s₃.gpr .rcx = s₁.gpr .rcx := (k3.1 _ (by simp [Ne.symm h1c])).trans C2
  have C4 : s₄.gpr .rcx = s₁.gpr .rcx := (k4.1 _ (by simp [Ne.symm h2c])).trans C3
  have r0_1 : s₁.gpr r0 = s.gpr r0 := k1.1 _ (by simp [h0c, h0b])
  have r0_5 : s₅.gpr r0 = s₂.gpr r0 := by
    rw [k5.1 _ (by simp [h03, h0b, h0a, h0d]), k4.1 _ (by simp [h02, h0b, h0a, h0d]),
      k3.1 _ (by simp [h01, h0b, h0a, h0d])]
  have r1_2 : s₂.gpr r1 = s.gpr r1 := by
    rw [k2.1 _ (by simp [Ne.symm h01, h1b, h1a, h1d]), k1.1 _ (by simp [h1c, h1b])]
  have r1_5 : s₅.gpr r1 = s₃.gpr r1 := by
    rw [k5.1 _ (by simp [h13, h1b, h1a, h1d]), k4.1 _ (by simp [h12, h1b, h1a, h1d])]
  have r2_3 : s₃.gpr r2 = s.gpr r2 := by
    rw [k3.1 _ (by simp [Ne.symm h12, h2b, h2a, h2d]), k2.1 _ (by simp [Ne.symm h02, h2b, h2a, h2d]),
      k1.1 _ (by simp [h2c, h2b])]
  have r2_5 : s₅.gpr r2 = s₄.gpr r2 := k5.1 _ (by simp [h23, h2b, h2a, h2d])
  have r3_4 : s₄.gpr r3 = s.gpr r3 := by
    rw [k4.1 _ (by simp [Ne.symm h23, h3b, h3a, h3d]), k3.1 _ (by simp [Ne.symm h13, h3b, h3a, h3d]),
      k2.1 _ (by simp [Ne.symm h03, h3b, h3a, h3d]), k1.1 _ (by simp [h3c, h3b])]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [M1, M2, M3, M4, C2, C3, C4, c1, b1, r0_1, r1_2, r2_3, r3_4, z, Nat.mul_zero,
      Nat.add_zero, Nat.mul_one, Nat.reduceMul, word] at e2 e3 e4 e5
    simp only [val4, fe, word, RegUpd.gpr_setReg_of_ne _ _ h04, RegUpd.gpr_setReg_of_ne _ _ h14,
      RegUpd.gpr_setReg_of_ne _ _ h24, RegUpd.gpr_setReg_of_ne _ _ h34, r0_5, r1_5, r2_5]
    have hp : ∀ x y z w v : Nat, v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
        v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by intros; ring
    rw [hp]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2.1]
    rw [k5.1 _ (by simp [hr.2.2.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k4.1 _ (by simp [hr.2.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k3.1 _ (by simp [hr.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k2.1 _ (by simp [hr.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k1.1 _ (by simp [hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · exact k5.2.1.trans M4
  · rw [RegUpd.rd_setReg, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [RegUpd.wr_setReg, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]

/-! ## The reduction -/

/-- `reduce`, with its steps spelled out. -/
theorem reduce_eq : reduce =
    ([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] : List Instr) ++ (mulStep .r8 .rbp .rcx (.reg .r12) ++
      (mulStep .r9 .rbp .rcx (.reg .r13) ++ (mulStep .r10 .rbp .rcx (.reg .r14) ++
        (mulStep .r11 .rbp .rcx (.reg .r15) ++ fold)))) := by
  simp only [reduce, List.append_assoc]
  rfl

/-- `lo + 38 hi` of the eight words `r8–r15`: into `r8–r11` and the carry word
`rbp`. -/
theorem reduceSteps_ok (s : State) :
    WP isa (.block (([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] : List Instr) ++ (mulStep .r8 .rbp .rcx (.reg .r12) ++
      (mulStep .r9 .rbp .rcx (.reg .r13) ++ (mulStep .r10 .rbp .rcx (.reg .r14) ++
        mulStep .r11 .rbp .rcx (.reg .r15)))))) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .rbp).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) ∧
      s'.gpr .rcx = 38 ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)]) s
      (fun s' => s'.gpr .rcx = 38 ∧ s'.gpr .rbp = 0 ∧ Keeps [.rcx, .rbp] s s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
      exists_eq_left']
    refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]) fun s₁ ⟨c1, b1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₁ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₂ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₃ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  refine WP.mono (mulStep_ok s₄ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₅ ⟨e5, k5⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s₅ :=
    (((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide)) |>.trans (k5.mono (by decide))
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  refine ⟨?_, ?_, K⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [c1, g k1 .r12 (by decide), b1, g k1 .r8 (by decide)] at e2
    rw [g k2 .rcx (by decide), c1, g k2 .r13 (by decide), g k1 .r13 (by decide),
      g k2 .r9 (by decide), g k1 .r9 (by decide)] at e3
    rw [g k3 .rcx (by decide), g k2 .rcx (by decide), c1, g k3 .r14 (by decide),
      g k2 .r14 (by decide), g k1 .r14 (by decide), g k3 .r10 (by decide), g k2 .r10 (by decide),
      g k1 .r10 (by decide)] at e4
    rw [g k4 .rcx (by decide), g k3 .rcx (by decide), g k2 .rcx (by decide), c1,
      g k4 .r15 (by decide), g k3 .r15 (by decide), g k2 .r15 (by decide), g k1 .r15 (by decide),
      g k4 .r11 (by decide), g k3 .r11 (by decide), g k2 .r11 (by decide),
      g k1 .r11 (by decide)] at e5
    simp only [val4, g k5 .r8 (by decide), g k4 .r8 (by decide), g k3 .r8 (by decide),
      g k5 .r9 (by decide), g k4 .r9 (by decide), g k5 .r10 (by decide)]
    have h38 : (38 : BitVec 64).toNat = 38 := rfl
    rw [h38] at e2 e3 e4 e5
    rw [z] at e2
    omega
  · rw [g k5 .rcx (by decide), g k4 .rcx (by decide), g k3 .rcx (by decide), g k2 .rcx (by decide), c1]

/-- `fold`: `r8–r11 + 38 rbp`, with `rcx = 38` and `rbp < 2⁵²`. -/
theorem fold_ok (s : State) (hc : s.gpr .rcx = 38) (hb : (s.gpr .rbp).toNat < 2 ^ 52) :
    WP isa (.block fold) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % VG.Spec.X25519.P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 38 * (s.gpr .rbp).toNat) %
          VG.Spec.X25519.P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx] s s' := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rax (.reg .rbp), .mul .rcx]) s (fun s' =>
      (s'.gpr .rax).toNat = 38 * (s.gpr .rbp).toNat ∧ Keeps [.rax, .rdx] s s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, execMul,
      RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
      exists_eq_left', hc]
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · rw [BitVec.toNat_ofNat, show (38 : BitVec 64).toNat = 38 from rfl, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (carry38_ok s₁ (by omega)) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans (k2.mono (by decide))⟩
  rw [e2, e1, k1.1 .r8 (by decide), k1.1 .r9 (by decide), k1.1 .r10 (by decide),
    k1.1 .r11 (by decide)]

end VG.Proof.X25519.X86_64

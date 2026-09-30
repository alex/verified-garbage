import VerifiedGarbage.Proof.X25519.X86_64.Ops

/-!
# X25519 on x86-64: addition and subtraction

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem ld_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (off base d) 8 :=
  ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

/-- The sum of `[a]` and `[b]` into `r8–r11`, and `38 ×` its carry into `rax`. -/
theorem addPre_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * c =
          fe s.mem base a + fe s.mem base b ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, ld_sc hs (d := a) (by omega),
    ld_sc hs (d := b) (by omega), ld_sc hs (d := a + 8) (by omega),
    ld_sc hs (d := b + 8) (by omega), ld_sc hs (d := a + 16) (by omega),
    ld_sc hs (d := b + 16) (by omega), ld_sc hs (d := a + 24) (by omega),
    ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact chain_add _ _ _ _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `[o] = [a] + [b]`. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (add o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a + F s.mem base b := by
  rw [show add o a b = [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++ (carry38 ++ store4 o) from rfl,
    WP.block_append_iff]
  refine WP.mono (addPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry38_ok s₁ (by omega)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, k2.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1])]
  · rw [rd3, k2.2.2.1, k1.2.2.1]
  · rw [wr3, k2.2.2.2, k1.2.2.2]
  · rw [m3, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_add
    rw [m3, fe_st4 _ _ (by omega), e2, x1, ← e1, fold256]

/-- The difference of `[a]` and `[b]` into `r8–r11`, and `38 ×` its borrow
into `rax`. -/
theorem subPre_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + fe s.mem base b =
          fe s.mem base a + 2 ^ 256 * c ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, ld_sc hs (d := a) (by omega),
    ld_sc hs (d := b) (by omega), ld_sc hs (d := a + 8) (by omega),
    ld_sc hs (d := b + 8) (by omega), ld_sc hs (d := a + 16) (by omega),
    ld_sc hs (d := b + 16) (by omega), ld_sc hs (d := a + 24) (by omega),
    ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact chain_sub _ _ _ _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `r8–r11 - rax`, and `38 ×` its borrow into `rax`. -/
theorem borrow38_ok (s : State) :
    WP isa (.block [.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + (s.gpr .rax).toNat =
          val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * c ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_sub (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) 0 0 0
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [val4, hz, Nat.mul_zero, Nat.add_zero] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `r8 - rax`, when it does not borrow. -/
theorem subLow_ok (s : State) (h : (s.gpr .rax).toNat ≤ (s.gpr .r8).toNat) :
    WP isa (.block [.alu .sub .r8 (.reg .rax)]) s fun s' =>
      (s'.gpr .r8).toNat + (s.gpr .rax).toNat = (s.gpr .r8).toNat ∧ Keeps [.r8] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_sub]
    have := (s.gpr .r8).isLt
    rw [show 2 ^ 64 - (s.gpr .rax).toNat + (s.gpr .r8).toNat =
      (s.gpr .r8).toNat - (s.gpr .rax).toNat + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `[o] = [a] - [b]`. -/
theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (sub o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a - F s.mem base b := by
  rw [show sub o a b = [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      ([.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      ([.alu .sub .r8 (.reg .rax)] ++ store4 o)) from rfl, WP.block_append_iff]
  refine WP.mono (subPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (borrow38_ok s₁) fun s₂ ⟨c', hc', e2, x2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hlow : (s₂.gpr .rax).toNat ≤ (s₂.gpr .r8).toNat := by
    rw [x2]
    rcases Nat.lt_or_ge c' 1 with h | h
    · omega
    · simp only [val4] at e2
      have := (s₂.gpr .r9).isLt; have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
      have := (s₁.gpr .r8).isLt; have := (s₁.gpr .r9).isLt; have := (s₁.gpr .r10).isLt
      have := (s₁.gpr .r11).isLt
      omega
  rw [WP.block_append_iff]
  refine WP.mono (subLow_ok s₂ hlow) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (store4_ok hs₃ ho) fun s₄ ⟨m4, g4, rd4, wr4⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4, k3.1 r (by simp [hr.2.2.2.2.1]),
      k2.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]),
      k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
  · rw [rd4, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wr4, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [m4, k3.2.1, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_sub
    rw [m4, fe_st4 _ _ (by omega)]
    have r9 := k3.1 .r9 (by decide); have r10 := k3.1 .r10 (by decide)
    have r11 := k3.1 .r11 (by decide)
    simp only [val4] at e1 e2 ⊢
    rw [r9, r10, r11]
    rw [x1] at e2
    rw [x2] at e3
    simp only [VG.Spec.X25519.P]
    omega

end VG.Proof.X25519.X86_64

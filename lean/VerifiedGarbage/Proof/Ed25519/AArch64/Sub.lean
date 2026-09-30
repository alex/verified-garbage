import VerifiedGarbage.Proof.Ed25519.AArch64.Ops

/-! Untrusted: four-word field subtraction. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

/-- Read both operands before any stores, so destination aliases are valid. -/
theorem subWords_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : FieldRange a) (hb : FieldRange b) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block (fieldSubWords a b)) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + fe s.mem base b =
          fe s.mem base a + 2 ^ 256 * (1 - c.toNat) ∧
        (t.gpr .x8).toNat = 38 * (1 - c.toNat) ∧ Keeps [.x4, .x5, .x6, .x7, .x8, .x9] s t := by
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have w : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩
  have enc : ∀ d, d + 8 ≤ 8192 → d < 4096 * Size.x.bytes := by
    intro d hd
    change d < 32768
    omega
  apply WP.of_runBlock
  simp only [fieldSubWords, borrowValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, ld, exec, addr, State.load, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.mem_addWithCarry,
    BitVec.setWidth_eq, hs.x0, hz, h38, Size.bytes,
    Nat.add_mod, ha, hb, Nat.reduceMod, Nat.zero_add,
    enc a (by omega), enc b (by omega), enc (a + 8) (by omega), enc (b + 8) (by omega),
    enc (a + 16) (by omega), enc (b + 16) (by omega), enc (a + 24) (by omega), enc (b + 24) (by omega),
    w a (by omega), w b (by omega), w (a + 8) (by omega), w (b + 8) (by omega),
    w (a + 16) (by omega), w (b + 16) (by omega), w (a + 24) (by omega), w (b + 24) (by omega),
    and_self, ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨carryOut (word s.mem base (a + 24)) (~~~word s.mem base (b + 24))
    (carryOut (word s.mem base (a + 16)) (~~~word s.mem base (b + 16))
      (carryOut (word s.mem base (a + 8)) (~~~word s.mem base (b + 8))
        (carryOut (word s.mem base a) (~~~word s.mem base b) true))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := sub4_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) true
    dsimp only [fe, word, Mem.readW, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [word, Mem.readW, carryOut, Size.bits]
    exact borrow38_value _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem borrow38_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block borrow38) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + (s.gpr .x8).toNat =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 2 ^ 256 * (1 - c.toNat) ∧
        (t.gpr .x8).toNat = 38 * (1 - c.toNat) ∧ Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  apply WP.of_runBlock
  simp only [borrow38, borrowValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, h38,
    Option.some.injEq, exists_eq_left']
  refine ⟨carryOut (s.gpr .x7) (~~~0)
    (carryOut (s.gpr .x6) (~~~0) (carryOut (s.gpr .x5) (~~~0)
      (carryOut (s.gpr .x4) (~~~s.gpr .x8) true))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := sub4_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) 0 0 0 true
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [carryOut, Size.bits]
    exact borrow38_value _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem subLow_ok (s : State) (h : (s.gpr .x8).toNat ≤ (s.gpr .x4).toNat) :
    WP isa (.block [.sub .x .x4 .x4 .x8]) s fun t =>
      (t.gpr .x4).toNat + (s.gpr .x8).toNat = (s.gpr .x4).toNat ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.toNat_sub]
    have := (s.gpr .x4).isLt
    omega
  · intro r hr
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-- Subtraction modulo p, including both possible borrow corrections. -/
theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : FieldRange o) (ha : FieldRange a) (hb : FieldRange b) :
    WP isa (.block (fieldSub o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  rw [fieldSub, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (subWords_ok hs₀ ha hb hz h38) fun s₁ ⟨c, e1, x1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  have h381 : s₁.gpr .x11 = 38 := (k1.gpr _ (by decide)).trans h38
  refine WP.mono (borrow38_ok s₁ hz1 h381) fun s₂ ⟨c', e2, x2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hlow : (s₂.gpr .x8).toNat ≤ (s₂.gpr .x4).toNat := by
    rw [x2]
    have hc := Bool.toNat_le c
    have hc' := Bool.toNat_le c'
    have h5 := (s₂.gpr .x5).isLt
    have h6 := (s₂.gpr .x6).isLt
    have h7 := (s₂.gpr .x7).isLt
    have e := e2
    rw [x1] at e
    simp only [val4] at e
    omega_using [hc, hc', h5, h6, h7, e]
  rw [WP.block_append_iff]
  refine WP.mono (subLow_ok s₂ hlow) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (store4_ok hs₃ ho) fun s₄ heq => ?_
  subst s₄
  have k0' : Keeps clob s s₀ := k0.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  have k1' : Keeps clob s₀ s₁ := k1.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have k2' : Keeps clob s₁ s₂ := k2.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have k3' : Keeps clob s₂ s₃ := k3.mono (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    decide)
  refine ⟨Op.of_store ho (k0'.trans (k1'.trans (k2'.trans k3'))) _ _ _ _, ?_⟩
  simp only [F]
  apply toFe_sub
  rw [fe_st4 _ _ (by have := ho.2; omega)]
  have r5 := k3.gpr .x5 (by decide)
  have r6 := k3.gpr .x6 (by decide)
  have r7 := k3.gpr .x7 (by decide)
  rw [k0.mem] at e1
  simp only [val4] at e1 e2 ⊢
  rw [r5, r6, r7]
  rw [x1] at e2
  rw [x2] at e3
  simp only [VG.Spec.X25519.P]
  omega_using [e1, e2, e3]

end VG.Proof.Ed25519.AArch64

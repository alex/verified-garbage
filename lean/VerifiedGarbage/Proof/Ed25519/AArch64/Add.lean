import VerifiedGarbage.Proof.Ed25519.AArch64.Ops

/-! Untrusted: four-word field addition. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

/-- Read both operands before any stores, so destination aliases are valid. -/
theorem addWords_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : FieldRange a) (hb : FieldRange b) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block (fieldAddWords a b)) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * c.toNat =
          fe s.mem base a + fe s.mem base b ∧
        (t.gpr .x8).toNat = 38 * c.toNat ∧ Keeps [.x4, .x5, .x6, .x7, .x8, .x9] s t := by
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have w : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩
  have enc : ∀ d, d + 8 ≤ 8192 → d < 4096 * Size.x.bytes := by
    intro d hd
    change d < 32768
    omega
  apply WP.of_runBlock
  simp only [fieldAddWords, carryValue38, List.cons_append, List.nil_append,
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
  refine ⟨carryOut (word s.mem base (a + 24)) (word s.mem base (b + 24))
    (carryOut (word s.mem base (a + 16)) (word s.mem base (b + 16))
      (carryOut (word s.mem base (a + 8)) (word s.mem base (b + 8))
        (carryOut (word s.mem base a) (word s.mem base b) false))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := add4_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) false
    dsimp only [fe, word, Mem.readW, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [word, Mem.readW, carryOut, Size.bits]
    exact carry38_value _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- Addition modulo p, with memory and ABI frames. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : FieldRange o) (ha : FieldRange a) (hb : FieldRange b) :
    WP isa (.block (fieldAdd o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  rw [fieldAdd, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addWords_ok hs₀ ha hb hz h38) fun s₁ ⟨c, e1, x1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  have h381 : s₁.gpr .x11 = 38 := (k1.gpr _ (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by
    rw [x1]
    have := Bool.toNat_le c
    omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ heq => ?_
  subst s₃
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
  refine ⟨Op.of_store ho (k0'.trans (k1'.trans k2')) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega), e2, x1]
  rw [k0.mem] at e1
  have hm : toFe (val4 (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7) + 38 * c.toNat) =
      toFe (fe s.mem base a + fe s.mem base b) := by
    apply toFe_congr
    rw [← e1]
    exact (fold256 _ _).symm
  exact hm.trans (toFe_add rfl)

end VG.Proof.Ed25519.AArch64

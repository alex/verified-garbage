import VerifiedGarbage.Proof.X25519.X86_64.Inv

/-!
# X25519 on x86-64: the full reduction

Untrusted: everything here is checked by Lean. `freeze a` leaves in
`r8–r11` the residue of `[a]` below `p`: bit 255 folded in as 19 gives
`x < 2²⁵⁵ + 19`, then `x + 19 - 2²⁵⁵` (which is `x - p`) is selected if it is
not negative.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519
open VG.Spec.X25519 (P)

/-- The fold of bit 255. -/
def freezeA (a : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .mov .r9 (.mem (sc (a + 8))), .mov .r10 (.mem (sc (a + 16))),
    .mov .r11 (.mem (sc (a + 24))),
    .mov .rax (.reg .r11), .shift .shr .rax 63, .movImm64 .rdx low63, .alu .and .r11 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .and .rcx (.imm 19),
    .alu .add .r8 (.reg .rcx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0)]

theorem fold_top (a0 a1 a2 a3 a3' m : BitVec 64) (hm : m.toNat = 19 * (a3.toNat / 2 ^ 63))
    (hl : a3'.toNat = a3.toNat % 2 ^ 63) :
    let c0 := decide (2 ^ 64 ≤ a0.toNat + m.toNat)
    let c1 := decide (2 ^ 64 ≤ a1.toNat + (0 : BitVec 64).toNat + c0.toNat)
    let c2 := decide (2 ^ 64 ≤ a2.toNat + (0 : BitVec 64).toNat + c1.toNat)
    let v := val4 (a0 + m) (a1 + 0 + (BitVec.ofBool c0).setWidth 64)
      (a2 + 0 + (BitVec.ofBool c1).setWidth 64) (a3' + 0 + (BitVec.ofBool c2).setWidth 64)
    v % P = val4 a0 a1 a2 a3 % P ∧ v < 2 ^ 255 + 19 := by
  intro c0 c1 c2 v
  have e := chain_add a0 a1 a2 a3' m 0 0 0
  change v + 2 ^ 256 * _ = _ at e
  clear_value v c2 c1 c0
  have h0 := a0.isLt; have h1 := a1.isLt; have h2 := a2.isLt; have h3 := a3.isLt
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [val4, hz] at e
  have hv : val4 a0 a1 a2 a3 = v + P * (a3.toNat / 2 ^ 63) := by
    simp only [val4, P]; omega
  exact ⟨by rw [hv, Nat.add_mul_mod_self_left], by omega⟩

theorem and_low63 (x : BitVec 64) : (x &&& low63).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_and, show low63.toNat = 2 ^ 63 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem freezeA_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (freezeA a)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P = fe s.mem base a % P ∧
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) < 2 ^ 255 + 19 ∧
      s'.gpr .rdx = low63 ∧ Keeps [.r8, .r9, .r10, .r11, .rax, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [freezeA, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    execShift, State.load64, State.setReg32, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, hs.rdi, ld_sc hs (d := a) (by omega), ld_sc hs (d := a + 8) (by omega),
    ld_sc hs (d := a + 16) (by omega), ld_sc hs (d := a + 24) (by omega),
    show 1 ≤ 63 ∧ 63 ≤ 63 from ⟨by omega, by omega⟩, ite_true, ite_false, reduceCtorEq, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', se0]
  have ht : ∀ x : BitVec 64, (x >>> 63).toNat = x.toNat / 2 ^ 63 := fun x => by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hm : ∀ x : BitVec 64,
      (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 &&& BitVec.signExtend 64 (19 : BitVec 32)).toNat =
        19 * (x.toNat / 2 ^ 63) := fun x => by
    have hx := x.isLt
    rcases (by omega : x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1) with h | h
    · rw [BitVec.eq_of_toNat_eq (show (x >>> 63).toNat = (0 : BitVec 64).toNat by rw [ht, h]; rfl), h]
      decide
    · rw [BitVec.eq_of_toNat_eq (show (x >>> 63).toNat = (1 : BitVec 64).toNat by rw [ht, h]; rfl), h]
      decide
  obtain ⟨e₁, e₂⟩ := fold_top _ _ _ _ _ _ (hm _) (and_low63 (s.mem.readW (off base (a + 24)) 64))
  refine ⟨e₁, e₂, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
    hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- `x + 19` into `r12–r15`, and the mask of its bit 255 (`x ≥ p`) into `rcx`,
with the bit cleared. -/
def freezeB : List Instr :=
  [.mov .r12 (.reg .r8), .alu .add .r12 (.imm 19), .mov .r13 (.reg .r9), .alu .adc .r13 (.imm 0),
    .mov .r14 (.reg .r10), .alu .adc .r14 (.imm 0), .mov .r15 (.reg .r11),
    .alu .adc .r15 (.imm 0),
    .mov .rax (.reg .r15), .shift .shr .rax 63, .alu .and .r15 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax)]

theorem add19_top (a0 a1 a2 a3 : BitVec 64) (hx : val4 a0 a1 a2 a3 < 2 ^ 255 + 19) :
    let b := BitVec.signExtend 64 (19 : BitVec 32)
    let c0 := decide (2 ^ 64 ≤ a0.toNat + b.toNat)
    let c1 := decide (2 ^ 64 ≤ a1.toNat + (0 : BitVec 64).toNat + c0.toNat)
    let c2 := decide (2 ^ 64 ≤ a2.toNat + (0 : BitVec 64).toNat + c1.toNat)
    let w3 := a3 + 0 + (BitVec.ofBool c2).setWidth 64
    BitVec.setWidth 64 (0 : BitVec 32) - w3 >>> 63 = mask (decide (P ≤ val4 a0 a1 a2 a3)) ∧
    (P ≤ val4 a0 a1 a2 a3 → val4 (a0 + b) (a1 + 0 + (BitVec.ofBool c0).setWidth 64)
      (a2 + 0 + (BitVec.ofBool c1).setWidth 64) (w3 &&& low63) = val4 a0 a1 a2 a3 - P) := by
  intro b c0 c1 c2 w3
  have e := chain_add a0 a1 a2 a3 b 0 0 0
  change val4 _ _ _ w3 + 2 ^ 256 * _ = _ at e
  clear_value w3 c2
  generalize a0 + b = w0 at e ⊢
  generalize a1 + 0 + (BitVec.ofBool c0).setWidth 64 = w1 at e ⊢
  generalize a2 + 0 + (BitVec.ofBool c1).setWidth 64 = w2 at e ⊢
  have hb : b.toNat = 19 := rfl
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  simp only [val4, hb, hz] at e hx ⊢
  have ht : (w3 >>> 63).toNat = w3.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hl := and_low63 w3
  by_cases h : P ≤ a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat
  · have h1' : w3.toNat / 2 ^ 63 = 1 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (1 : BitVec 64).toNat by rw [ht, h1']; rfl),
      decide_eq_true h]
    refine ⟨by decide, fun _ => ?_⟩
    rw [hl]; simp only [P] at h ⊢; omega
  · have h0' : w3.toNat / 2 ^ 63 = 0 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (0 : BitVec 64).toNat by rw [ht, h0']; rfl),
      decide_eq_false h]
    exact ⟨by decide, fun h' => absurd h' h⟩

theorem freezeB_ok (s : State)
    (hx : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) < 2 ^ 255 + 19)
    (hd : s.gpr .rdx = low63) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .rcx = mask (decide (P ≤ val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11))) ∧
      (P ≤ val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) →
        val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) =
          val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) - P) ∧
      Keeps [.r12, .r13, .r14, .r15, .rax, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [freezeB, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    execShift, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, hd, show 1 ≤ 63 ∧ 63 ≤ 63 from ⟨by omega, by omega⟩,
    ite_true, ite_false, reduceCtorEq, and_self, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', se0]
  obtain ⟨e₁, e₂⟩ := add19_top _ _ _ _ hx
  refine ⟨e₁, e₂, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
    hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- The selection by the mask `rcx`. -/
def freezeC : List Instr :=
  [.alu .xor .r12 (.reg .r8), .alu .and .r12 (.reg .rcx), .alu .xor .r8 (.reg .r12),
    .alu .xor .r13 (.reg .r9), .alu .and .r13 (.reg .rcx), .alu .xor .r9 (.reg .r13),
    .alu .xor .r14 (.reg .r10), .alu .and .r14 (.reg .rcx), .alu .xor .r10 (.reg .r14),
    .alu .xor .r15 (.reg .r11), .alu .and .r15 (.reg .rcx), .alu .xor .r11 (.reg .r15)]

theorem xor_sel' (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((b ^^^ a) &&& mask sw) = if sw then b else a := by
  rw [BitVec.xor_comm b a]; exact (xor_sel sw a b).1

theorem freezeC_ok (s : State) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block freezeC) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        (if sw then val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)
          else val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' := by
  apply WP.of_runBlock
  simp only [freezeC, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hm, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left', xor_sel']
  refine ⟨by cases sw <;> rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem freeze_eq (a : Nat) : freeze a = freezeA a ++ (freezeB ++ freezeC) := rfl

/-- `freeze a`: `r8–r11` is `[a] mod p`. -/
theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (freeze a)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) = fe s.mem base a % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax, .rcx, .rdx] s s' := by
  rw [freeze_eq, WP.block_append_iff]
  refine WP.mono (freezeA_ok hs ha) fun s₁ ⟨e₁, l₁, d₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (freezeB_ok s₁ l₁ d₁) fun s₂ ⟨m₂, y₂, k₂⟩ => ?_
  refine WP.mono (freezeC_ok s₂ m₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [k₂.1 .r8 (by decide), k₂.1 .r9 (by decide), k₂.1 .r10 (by decide),
    k₂.1 .r11 (by decide)] at v₃
  refine ⟨?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))⟩
  rw [v₃, ← e₁]
  generalize val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) = x at l₁ y₂ ⊢
  by_cases h : P ≤ x
  · simp only [decide_eq_true h, ite_true]
    rw [y₂ h]; simp only [P] at h l₁ ⊢; omega
  · simp only [decide_eq_false h, Bool.false_eq_true, ite_false]
    exact (Nat.mod_eq_of_lt (by omega)).symm

end VG.Proof.X25519.X86_64

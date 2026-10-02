import VerifiedGarbage.Proof.X25519.X86_64.AddSub

/-!
# X25519 on x86-64: multiplication by `a24`, and the swap
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem mulSmall_eq (o a : Nat) (k : BitVec 32) : mulSmall o a k =
    zero4 ++ (([.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] : List Instr) ++
      (mulStep .r8 .rbp .rcx (.mem (sc (a + 8 * 0))) ++ (mulStep .r9 .rbp .rcx (.mem (sc (a + 8 * 1))) ++
        (mulStep .r10 .rbp .rcx (.mem (sc (a + 8 * 2))) ++
          (mulStep .r11 .rbp .rcx (.mem (sc (a + 8 * 3))) ++
            (([.mov32 .rcx (.imm 38)] : List Instr) ++ (fold ++ store4 o))))))) := by
  simp only [mulSmall, List.append_assoc]
  rfl

/-- `k · [a]` into `r8–r11` and the carry word `rbp`, with `r8–r11 = 0`. -/
theorem smallSteps_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a)
    (k : BitVec 32) (h0 : s.gpr .r8 = 0) (h1 : s.gpr .r9 = 0) (h2 : s.gpr .r10 = 0)
    (h3 : s.gpr .r11 = 0) :
    WP isa (.block (([.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] : List Instr) ++
      (mulStep .r8 .rbp .rcx (.mem (sc (a + 8 * 0))) ++ (mulStep .r9 .rbp .rcx (.mem (sc (a + 8 * 1))) ++
        (mulStep .r10 .rbp .rcx (.mem (sc (a + 8 * 2))) ++
          mulStep .r11 .rbp .rcx (.mem (sc (a + 8 * 3)))))))) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .rbp).toNat =
        k.toNat * fe s.mem base a ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s' := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)]) s
      (fun s' => s'.gpr .rcx = k.setWidth 64 ∧ s'.gpr .rbp = 0 ∧ Keeps [.rcx, .rbp] s s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
      exists_eq_left']
    refine ⟨by trivial, by trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]) fun s₁ ⟨c1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₁ (readSrc_sc hs₁ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₂ (readSrc_sc hs₂ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₃ (readSrc_sc hs₃ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  refine WP.mono (mulStep_ok s₄ (readSrc_sc hs₄ (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₅ ⟨e5, k5⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide)) |>.trans (k5.mono (by decide))⟩
  have M1 : s₁.mem = s.mem := k1.2.1
  have M2 : s₂.mem = s.mem := k2.2.1.trans M1
  have M3 : s₃.mem = s.mem := k3.2.1.trans M2
  have M4 : s₄.mem = s.mem := k4.2.1.trans M3
  have C2 : s₂.gpr .rcx = s₁.gpr .rcx := g k2 .rcx (by decide)
  have C3 : s₃.gpr .rcx = s₁.gpr .rcx := (g k3 .rcx (by decide)).trans C2
  have C4 : s₄.gpr .rcx = s₁.gpr .rcx := (g k4 .rcx (by decide)).trans C3
  have z : (0 : BitVec 64).toNat = 0 := rfl
  have hk : (k.setWidth 64).toNat = k.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le k.isLt (by decide))]
  rw [g k1 .r8 (by decide), h0] at e2
  rw [g k2 .r9 (by decide), g k1 .r9 (by decide), h1] at e3
  rw [g k3 .r10 (by decide), g k2 .r10 (by decide), g k1 .r10 (by decide), h2] at e4
  rw [g k4 .r11 (by decide), g k3 .r11 (by decide), g k2 .r11 (by decide), g k1 .r11 (by decide),
    h3] at e5
  simp only [M1, M2, M3, M4, C2, C3, C4, c1, b1, z, hk, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.reduceMul, word] at e2 e3 e4 e5
  simp only [val4, fe, word, g k5 .r8 (by decide), g k4 .r8 (by decide), g k3 .r8 (by decide),
    g k5 .r9 (by decide), g k4 .r9 (by decide), g k5 .r10 (by decide)]
  have hp : ∀ x y z w v : Nat, v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
      v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by intros; ring
  rw [hp]
  omega

/-- `[o] = a24 · [a]`. -/
theorem mulA24_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (mulSmall o a a24)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = Spec.X25519.a24 * F s.mem base a := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [mulSmall_eq, WP.block_append_iff]
  refine WP.mono (zero4_ok s) fun s₀ ⟨z8, z9, z10, z11, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (smallSteps_ok hs₀ ha a24 z8 z9 z10 z11) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm 38)]) s₁
      (fun s' => s'.gpr .rcx = 38 ∧ Keeps [.rcx] s₁ s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨by trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨c2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hc : (s₂.gpr .rbp).toNat < 2 ^ 52 := by
    rw [g k2 .rbp (by decide)]
    have hA : fe s₀.mem base a < 2 ^ 256 := by
      simp only [X86_64.fe, val4]
      have := (word s₀.mem base a).isLt; have := (word s₀.mem base (a + 8)).isLt
      have := (word s₀.mem base (a + 16)).isLt; have := (word s₀.mem base (a + 24)).isLt
      omega
    have h24 : a24.toNat = 121665 := rfl
    rw [h24] at e1
    simp only [val4] at e1
    omega
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok s₂ c2 hc) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (store4_ok hs₃ ho) fun s₄ ⟨m4, g4, rd4, wr4⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hr
    rw [g4, g k3 r (by simp [h1, h3, h5, h6, h7, h8]), g k2 r (by simp [h2]),
      g k1 r (by simp [h1, h2, h3, h4, h5, h6, h7, h8]), g k0 r (by simp [h5, h6, h7, h8])]
  · rw [rd4, k3.2.2.1, k2.2.2.1, k1.2.2.1, k0.2.2.1]
  · rw [wr4, k3.2.2.2, k2.2.2.2, k1.2.2.2, k0.2.2.2]
  · rw [m4, k3.2.1, k2.2.1, k1.2.1, k0.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_a24
    rw [m4, fe_st4 _ _ (by omega), e3, ← k0.2.1, g k2 .r8 (by decide), g k2 .r9 (by decide),
      g k2 .r10 (by decide), g k2 .r11 (by decide), g k2 .rbp (by decide),
      show (121665 : Nat) = a24.toNat from rfl, ← e1, fold256]

/-! ## The conditional swap -/

/-- The mask of a swap bit: all ones for a swap, zero otherwise. -/
def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cswap_eq (x y : Nat) : cswap x y =
    (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
      ([.mov .rax (.reg .r8), .alu .xor .rax (.reg .r12), .alu .and .rax (.reg .rcx),
        .alu .xor .r8 (.reg .rax), .alu .xor .r12 (.reg .rax),
        .mov .rax (.reg .r9), .alu .xor .rax (.reg .r13), .alu .and .rax (.reg .rcx),
        .alu .xor .r9 (.reg .rax), .alu .xor .r13 (.reg .rax),
        .mov .rax (.reg .r10), .alu .xor .rax (.reg .r14), .alu .and .rax (.reg .rcx),
        .alu .xor .r10 (.reg .rax), .alu .xor .r14 (.reg .rax),
        .mov .rax (.reg .r11), .alu .xor .rax (.reg .r15), .alu .and .rax (.reg .rcx),
        .alu .xor .r11 (.reg .rax), .alu .xor .r15 (.reg .rax)] : List Instr)) ++
      (store4 x ++ stores y .r12 .r13 .r14 .r15) := by
  simp only [cswap, List.append_assoc]
  rfl

theorem cswapPre_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x)
    (hy : Slot y) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
      ([.mov .rax (.reg .r8), .alu .xor .rax (.reg .r12), .alu .and .rax (.reg .rcx),
        .alu .xor .r8 (.reg .rax), .alu .xor .r12 (.reg .rax),
        .mov .rax (.reg .r9), .alu .xor .rax (.reg .r13), .alu .and .rax (.reg .rcx),
        .alu .xor .r9 (.reg .rax), .alu .xor .r13 (.reg .rax),
        .mov .rax (.reg .r10), .alu .xor .rax (.reg .r14), .alu .and .rax (.reg .rcx),
        .alu .xor .r10 (.reg .rax), .alu .xor .r14 (.reg .rax),
        .mov .rax (.reg .r11), .alu .xor .rax (.reg .r15), .alu .and .rax (.reg .rcx),
        .alu .xor .r11 (.reg .rax), .alu .xor .r15 (.reg .rax)] : List Instr))) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        (if sw then fe s.mem base y else fe s.mem base x) ∧
      val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) =
        (if sw then fe s.mem base x else fe s.mem base y) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax] s s' := by
  apply WP.of_runBlock
  simp only [loads, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, execAlu, State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi, hm, ld_sc hs (d := x) (by omega),
    ld_sc hs (d := y) (by omega), ld_sc hs (d := x + 8) (by omega),
    ld_sc hs (d := y + 8) (by omega), ld_sc hs (d := x + 16) (by omega),
    ld_sc hs (d := y + 16) (by omega), ld_sc hs (d := x + 24) (by omega),
    ld_sc hs (d := y + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases sw <;> rfl
  · cases sw <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

/-- `[x], [y] = [y], [x]` if `sw` (the mask `rcx`), else unchanged. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x)
    (hy : Slot y) (hxy : x + 32 ≤ y ∨ y + 32 ≤ x) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap x y)) s fun s' =>
      (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∃ m₁, Outside base x 32 s.mem m₁ ∧ Outside base y 32 m₁ s'.mem ∧
        fe m₁ base x = (if sw then fe s.mem base y else fe s.mem base x)) ∧
      fe s'.mem base x = (if sw then fe s.mem base y else fe s.mem base x) ∧
      fe s'.mem base y = (if sw then fe s.mem base x else fe s.mem base y) := by
  rw [cswap_eq, WP.block_append_iff]
  refine WP.mono (cswapPre_ok hs hx hy hm) fun s₁ ⟨e1, e2, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₁ hx) fun s₂ ⟨m2, g2, rd2, wr2⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨(g2 _).trans hs₁.rdi, wr2 ▸ hs₁.wr, hs.nowrap⟩
  refine WP.mono (stores_ok hs₂ hy _ _ _ _) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  have o2 := st4_outside s₁.mem base (o := x) (by omega) (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10)
    (s₁.gpr .r11)
  have o3 := st4_outside s₂.mem base (o := y) (by omega) (s₂.gpr .r12) (s₂.gpr .r13) (s₂.gpr .r14)
    (s₂.gpr .r15)
  rw [← m2] at o2
  rw [← m3] at o3
  have hm1 : s₁.mem = s.mem := k1.2.1
  have fx : fe s₂.mem base x = (if sw then fe s.mem base y else fe s.mem base x) := by
    rw [m2, fe_st4 _ _ (by omega), e1]
  refine ⟨fun r hr => ?_, by rw [g3, g2, k1.1 .rcx (by decide)], ?_, ?_, ⟨s₂.mem, hm1 ▸ o2, o3, fx⟩,
    ?_, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, g2, k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2])]
  · rw [rd3, rd2, k1.2.2.1]
  · rw [wr3, wr2, k1.2.2.2]
  · rw [o3.fe hxy (by omega), fx]
  · rw [m3, fe_st4 _ _ (by omega), g2, g2, g2, g2, e2]

end VG.Proof.X25519.X86_64

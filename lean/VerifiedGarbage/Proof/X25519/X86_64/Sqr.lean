import VerifiedGarbage.Proof.X25519.X86_64.Ops

/-!
# X25519 on x86-64: squaring

Untrusted: everything here is checked by Lean. `sqr o a` in parts: the
products `a_i a_j` (`i < j`) as rows of `mul` (`sq1`–`sq3`), doubled
(`sqDbl`), the squares added (`diag`, for any two registers), and reduced as
in `mul`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The square of four words, by the products of their words (with no
power of two above `2²⁵⁶`, which `ring` would not evaluate). -/
theorem sq_words (x y z w : Nat) :
    (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
      x * x + 2 ^ 128 * (y * y) + 2 ^ 256 * (z * z) + 2 ^ 256 * (2 ^ 128 * (w * w)) +
        2 * (2 ^ 64 * (x * y) + 2 ^ 128 * (x * z) + 2 ^ 192 * (x * w) + 2 ^ 192 * (y * z) +
          2 ^ 256 * (y * w) + 2 ^ 256 * (2 ^ 64 * (z * w))) := by
  ring

theorem fe_lt (m : Mem) (base : Addr) (a : Nat) : fe m base a < 2 ^ 256 := by
  simp only [X86_64.fe, val4]
  have := (word m base a).isLt; have := (word m base (a + 8)).isLt
  have := (word m base (a + 16)).isLt; have := (word m base (a + 24)).isLt
  omega

/-- `mov32 r, 0`. -/
theorem zero_ok (s : State) (r : Reg) :
    WP isa (.block [.mov32 r (.imm 0)]) s fun s' => s'.gpr r = 0 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, fun q hq => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-- `mov d, rbp`. -/
theorem movRbp_ok (s : State) (d : Reg) :
    WP isa (.block [.mov d (.reg .rbp)]) s fun s' => s'.gpr d = s.gpr .rbp ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, fun q hq => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-! ## The products `a_i a_j` -/

theorem sq1_eq (a : Nat) : sq1 a = ([.mov .rcx (.mem (sc a)), .mov32 .rbp (.imm 0)] : List Instr) ++
    (([.mov32 .r9 (.imm 0)] : List Instr) ++ (([.mov32 .r10 (.imm 0)] : List Instr) ++
      (([.mov32 .r11 (.imm 0)] : List Instr) ++ (mulStep .r9 .rbp .rcx (.mem (sc (a + 8))) ++
        (mulStep .r10 .rbp .rcx (.mem (sc (a + 16))) ++ (mulStep .r11 .rbp .rcx (.mem (sc (a + 24))) ++
          ([.mov .r12 (.reg .rbp)] : List Instr))))))) := by
  simp only [sq1, List.append_assoc]; rfl

/-- `r9–r12 = a₀ · (a₁, a₂, a₃)`. -/
theorem sq1_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sq1 a)) s fun s' =>
      (s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat + 2 ^ 128 * (s'.gpr .r11).toNat +
          2 ^ 192 * (s'.gpr .r12).toNat =
        (word s.mem base a).toNat * (word s.mem base (a + 8)).toNat +
          2 ^ 64 * ((word s.mem base a).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 128 * ((word s.mem base a).toNat * (word s.mem base (a + 24)).toNat) ∧
      Keeps [.r9, .r10, .r11, .r12, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [sq1_eq, WP.block_append_iff]
  refine WP.mono (rowStart_ok hs (d := a) (by omega)) fun s1 ⟨c1, b1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s1 .r9) fun s2 ⟨z2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s2 .r10) fun s3 ⟨z3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s3 .r11) fun s4 ⟨z4, k4⟩ => ?_
  have hs4 := ((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s4 (readSrc_sc hs4 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s5 ⟨e5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s5 (readSrc_sc hs5 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s6 ⟨e6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s6 (readSrc_sc hs6 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s7 ⟨e7, k7⟩ => ?_
  refine WP.mono (movRbp_ok s7 .r12) fun s8 ⟨m8, k8⟩ => ?_
  refine ⟨?_, (((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans
    (k6.mono (by decide))).trans (k7.mono (by decide))).trans (k8.mono (by decide))⟩
  have M4 : s4.mem = s.mem := k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  have M6 : s6.mem = s.mem := k6.2.1.trans M5
  have C4 : s4.gpr .rcx = word s.mem base a := by
    rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), c1]
  have C5 : s5.gpr .rcx = word s.mem base a := (k5.1 _ (by decide)).trans C4
  have C6 : s6.gpr .rcx = word s.mem base a := (k6.1 _ (by decide)).trans C5
  have B4 : s4.gpr .rbp = 0 := by rw [k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), b1]
  have R9 : s4.gpr .r9 = 0 := by rw [k4.1 _ (by decide), k3.1 _ (by decide), z2]
  have R10 : s5.gpr .r10 = 0 := by rw [k5.1 _ (by decide), k4.1 _ (by decide), z3]
  have R11 : s6.gpr .r11 = 0 := by rw [k6.1 _ (by decide), k5.1 _ (by decide), z4]
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [M4, C4, B4, R9, hz] at e5
  rw [M5, C5, R10, hz] at e6
  rw [M6, C6, R11, hz] at e7
  rw [m8, k8.1 .r9 (by decide), k7.1 .r9 (by decide), k6.1 .r9 (by decide),
    k8.1 .r10 (by decide), k7.1 .r10 (by decide), k8.1 .r11 (by decide)]
  omega

theorem sq2_eq (a : Nat) : sq2 a = ([.mov .rcx (.mem (sc (a + 8))), .mov32 .rbp (.imm 0)] : List Instr) ++
    (mulStep .r11 .rbp .rcx (.mem (sc (a + 16))) ++ (mulStep .r12 .rbp .rcx (.mem (sc (a + 24))) ++
      ([.mov .r13 (.reg .rbp)] : List Instr))) := by
  simp only [sq2, List.append_assoc]

/-- `r11–r13 = r11–r12 + a₁ · (a₂, a₃)`. -/
theorem sq2_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sq2 a)) s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .r12).toNat + 2 ^ 128 * (s'.gpr .r13).toNat =
        (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat +
          (word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat +
          2 ^ 64 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat) ∧
      Keeps [.r11, .r12, .r13, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [sq2_eq, WP.block_append_iff]
  refine WP.mono (rowStart_ok hs (d := a + 8) (by omega)) fun s1 ⟨c1, b1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s1 (readSrc_sc hs1 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s2 (readSrc_sc hs2 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.mono (movRbp_ok s3 .r13) fun s4 ⟨m4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))⟩
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [k1.2.1, c1, b1, k1.1 .r11 (by decide), hz] at e2
  rw [k2.2.1, k1.2.1, k2.1 .rcx (by decide), c1, k2.1 .r12 (by decide), k1.1 .r12 (by decide)] at e3
  rw [m4, k4.1 .r11 (by decide), k3.1 .r11 (by decide), k4.1 .r12 (by decide)]
  omega

theorem sq3_eq (a : Nat) : sq3 a = ([.mov .rcx (.mem (sc (a + 16))), .mov32 .rbp (.imm 0)] : List Instr) ++
    (mulStep .r13 .rbp .rcx (.mem (sc (a + 24))) ++ ([.mov .r14 (.reg .rbp)] : List Instr)) := by
  simp only [sq3, List.append_assoc]

/-- `r13–r14 = r13 + a₂ a₃`. -/
theorem sq3_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sq3 a)) s fun s' =>
      (s'.gpr .r13).toNat + 2 ^ 64 * (s'.gpr .r14).toNat =
        (s.gpr .r13).toNat + (word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat ∧
      Keeps [.r13, .r14, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [sq3_eq, WP.block_append_iff]
  refine WP.mono (rowStart_ok hs (d := a + 16) (by omega)) fun s1 ⟨c1, b1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s1 (readSrc_sc hs1 (by omega)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.mono (movRbp_ok s2 .r14) fun s3 ⟨m3, k3⟩ => ?_
  refine ⟨?_, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [k1.2.1, c1, b1, k1.1 .r13 (by decide), hz] at e2
  rw [m3, k3.1 .r13 (by decide)]
  omega

/-! ## The doubling and the squares -/

/-- `r9–r15 = 2 · r9–r14`, `r8 = rbp = 0`. -/
theorem sqDbl_ok (s : State) :
    WP isa (.block sqDbl) s fun s' =>
      (s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat + 2 ^ 128 * (s'.gpr .r11).toNat +
          2 ^ 192 * (s'.gpr .r12).toNat + 2 ^ 256 * (s'.gpr .r13).toNat +
          2 ^ 256 * (2 ^ 64 * (s'.gpr .r14).toNat) + 2 ^ 256 * (2 ^ 128 * (s'.gpr .r15).toNat) =
        2 * ((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat + 2 ^ 128 * (s.gpr .r11).toNat +
          2 ^ 192 * (s.gpr .r12).toNat + 2 ^ 256 * (s.gpr .r13).toNat +
          2 ^ 256 * (2 ^ 64 * (s.gpr .r14).toNat)) ∧
      s'.gpr .r8 = 0 ∧ s'.gpr .rbp = 0 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [sqDbl, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    Option.map_some, Option.bind_some, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, by trivial, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · have e9 := add_carry (s.gpr .r9) (s.gpr .r9)
    have e10 := adc_carry (s.gpr .r10) (s.gpr .r10) (decide (2 ^ 64 ≤ (s.gpr .r9).toNat +
      (s.gpr .r9).toNat))
    have e11 := adc_carry (s.gpr .r11) (s.gpr .r11) (decide (2 ^ 64 ≤ (s.gpr .r10).toNat +
      (s.gpr .r10).toNat + (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat)).toNat))
    generalize (decide (2 ^ 64 ≤ (s.gpr .r11).toNat + (s.gpr .r11).toNat +
      (decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (s.gpr .r10).toNat +
        (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat)).toNat)).toNat)) = c11 at e11 ⊢
    have e12 := adc_carry (s.gpr .r12) (s.gpr .r12) c11
    generalize (decide (2 ^ 64 ≤ (s.gpr .r12).toNat + (s.gpr .r12).toNat + c11.toNat)) = c12
      at e12 ⊢
    have e13 := adc_carry (s.gpr .r13) (s.gpr .r13) c12
    generalize (decide (2 ^ 64 ≤ (s.gpr .r13).toNat + (s.gpr .r13).toNat + c12.toNat)) = c13
      at e13 ⊢
    have e14 := adc_carry (s.gpr .r14) (s.gpr .r14) c13
    generalize (decide (2 ^ 64 ≤ (s.gpr .r14).toNat + (s.gpr .r14).toNat + c13.toNat)) = c14
      at e14 ⊢
    have e15 := adc_carry (BitVec.setWidth 64 (0 : BitVec 32)) (BitVec.setWidth 64 (0 : BitVec 32))
      c14
    have hz : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
    rw [hz] at e15
    have := Bool.toNat_le c14
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

/-- The high half of a square is at most `2⁶⁴ - 2`. -/
theorem sq_hi_le (w : BitVec 64) : w.toNat * w.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
  have h := w.isLt
  have : w.toNat * w.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `diag t u d`: the square of the word at `d` added at `t` and `u`, with
the carry word `rbp` in and out. -/
theorem diag_ok {s : State} {base : Addr} (hs : Scr s base) {t u : Reg} {d : Nat}
    (hd : d + 8 ≤ 4096) (hta : t ≠ .rax) (htd : t ≠ .rdx) (htb : t ≠ .rbp) (hua : u ≠ .rax)
    (hud : u ≠ .rdx) (hub : u ≠ .rbp) (htu : t ≠ u) :
    WP isa (.block (diag t u d)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr u).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
        (s.gpr t).toNat + 2 ^ 64 * (s.gpr u).toNat + (s.gpr .rbp).toNat +
          (word s.mem base d).toNat * (word s.mem base d).toNat ∧
      Keeps [.rax, .rdx, t, u, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [diag, runBlock_cons, exec, readSrc_sc hs hd, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execMul,
    execAlu, Option.map_some, Option.bind_some, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    hta, htd, htb, hua, hud, hub, htu, Ne.symm htd, Ne.symm htb, Ne.symm hub, Ne.symm htu,
    ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · have hm := mulx_arith (word s.mem base d) (word s.mem base d)
    have hh := sq_hi_le (word s.mem base d)
    generalize hp : (word s.mem base d).toNat * (word s.mem base d).toNat = p at hm hh ⊢
    generalize hlo : BitVec.ofNat 64 p = lo at hm ⊢
    generalize hhi : BitVec.ofNat 64 (p / 2 ^ 64) = hi at hm ⊢
    have hhi' : hi.toNat ≤ 2 ^ 64 - 2 := by
      rw [← hhi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hh
    have e1 := add_carry lo (s.gpr .rbp)
    generalize decide (2 ^ 64 ≤ lo.toNat + (s.gpr .rbp).toNat) = c1 at e1 ⊢
    have e2 := adc_carry hi 0 c1
    have e3 := add_carry (s.gpr t) (lo + s.gpr .rbp)
    generalize decide (2 ^ 64 ≤ (s.gpr t).toNat + (lo + s.gpr .rbp).toNat) = c3 at e3 ⊢
    have e4 := adc_carry (s.gpr u) (hi + 0 + (BitVec.ofBool c1).setWidth 64) c3
    generalize decide (2 ^ 64 ≤ (s.gpr u).toNat + (hi + 0 + (BitVec.ofBool c1).setWidth 64).toNat +
      c3.toNat) = c4 at e4 ⊢
    have e5 := adc_carry ((0 : BitVec 32).setWidth 64) 0 c4
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have hz' : ((0 : BitVec 32).setWidth 64).toNat = 0 := rfl
    rw [hz] at e2 e5
    rw [hz'] at e5
    have := Bool.toNat_le c1; have := Bool.toNat_le c4
    have := Bool.toNat_le (decide (2 ^ 64 ≤ hi.toNat + 0 + c1.toNat))
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The square -/

open VG.Spec.X25519 (P) in
/-- `reduce`: `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`). -/
theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rdx, .rcx, .rbp] s s' := by
  rw [show reduce = ([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] ++
      (mulStep .r8 .rbp .rcx (.reg .r12) ++ (mulStep .r9 .rbp .rcx (.reg .r13) ++
        (mulStep .r10 .rbp .rcx (.reg .r14) ++ mulStep .r11 .rbp .rcx (.reg .r15))))) ++ fold by
      simp only [reduce_eq, List.append_assoc], WP.block_append_iff]
  refine WP.mono (reduceSteps_ok s) fun s₁ ⟨e1, c1, k1⟩ => ?_
  have hB : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
      38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := (s.gpr .r13).isLt
    have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt
    omega
  have hc : (s₁.gpr .rbp).toNat < 39 := by
    simp only [val4] at e1 hB
    have := (s₁.gpr .r8).isLt; have := (s₁.gpr .r9).isLt; have := (s₁.gpr .r10).isLt
    have := (s₁.gpr .r11).isLt
    omega
  refine WP.mono (fold_ok s₁ c1 (by omega)) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans (k2.mono (by decide))⟩
  rw [e2, ← fold256, e1, fold256]

theorem sqr_eq (o a : Nat) : sqr o a = sq1 a ++ (sq2 a ++ (sq3 a ++ (sqDbl ++
    (diag .r8 .r9 a ++ (diag .r10 .r11 (a + 8) ++ (diag .r12 .r13 (a + 16) ++
      (diag .r14 .r15 (a + 24) ++ (reduce ++ store4 o)))))))) := by
  simp only [sqr, List.append_assoc]

/-- `[o] = [a]²`. -/
theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a := by
  rw [sqr_eq, WP.block_append_iff]
  refine WP.mono (sq1_ok hs ha) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sq2_ok hs₁ ha) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sq3_ok hs₂ ha) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqDbl_ok s₃) fun s₄ ⟨e4, z4, b4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diag_ok hs₄ (d := a) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diag_ok hs₅ (d := a + 8) (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₆ ⟨e6, k6⟩ => ?_
  have hs₆ := hs₅.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diag_ok hs₆ (d := a + 16) (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₇ ⟨e7, k7⟩ => ?_
  have hs₇ := hs₆.of_keeps k7 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diag_ok hs₇ (d := a + 24) (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₈ ⟨e8, k8⟩ => ?_
  have hs₈ := hs₇.of_keeps k8 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s₈) fun s₉ ⟨e9, k9⟩ => ?_
  have hs₉ := hs₈.of_keeps k9 (by decide)
  refine WP.mono (store4_ok hs₉ ho) fun s₁₀ ⟨m10, g10, rd10, wr10⟩ => ?_
  have M : s₉.mem = s.mem := k9.2.1.trans (k8.2.1.trans (k7.2.1.trans (k6.2.1.trans
    (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)))))))
  have K : Keeps clob s s₉ :=
    ((((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))
  refine ⟨⟨fun r hr => by rw [g10, K.1 r hr], by rw [rd10, K.2.2.1], by rw [wr10, K.2.2.2], ?_⟩,
    ?_⟩
  · rw [m10, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m10, fe_st4 _ _ (by omega), e9]
    congr 1
    -- Every part read the same memory.
    have M4 : s₄.mem = s.mem := k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))
    rw [k1.2.1] at e2
    rw [k2.2.1, k1.2.1] at e3
    rw [M4] at e5
    rw [k5.2.1, M4] at e6
    rw [k6.2.1, k5.2.1, M4] at e7
    rw [k7.2.1, k6.2.1, k5.2.1, M4] at e8
    -- The registers along the way.
    rw [k3.1 .r9 (by decide), k2.1 .r9 (by decide), k3.1 .r10 (by decide), k2.1 .r10 (by decide),
      k3.1 .r11 (by decide), k3.1 .r12 (by decide)] at e4
    rw [z4, b4] at e5
    rw [k5.1 .r10 (by decide), k5.1 .r11 (by decide)] at e6
    rw [k6.1 .r12 (by decide), k5.1 .r12 (by decide), k6.1 .r13 (by decide),
      k5.1 .r13 (by decide)] at e7
    rw [k7.1 .r14 (by decide), k6.1 .r14 (by decide), k5.1 .r14 (by decide),
      k7.1 .r15 (by decide), k6.1 .r15 (by decide), k5.1 .r15 (by decide)] at e8
    have hb : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
      Nat.mul_lt_mul'' (fe_lt _ _ _) (fe_lt _ _ _)
    simp only [X86_64.fe, val4, sq_words] at hb ⊢
    rw [k8.1 .r8 (by decide), k7.1 .r8 (by decide), k6.1 .r8 (by decide), k8.1 .r9 (by decide),
      k7.1 .r9 (by decide), k6.1 .r9 (by decide), k8.1 .r10 (by decide), k7.1 .r10 (by decide),
      k8.1 .r11 (by decide), k7.1 .r11 (by decide), k8.1 .r12 (by decide), k8.1 .r13 (by decide)]
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz] at e5
    -- The products `a_i a_j` (`i < j`), then the squares added to their double.
    have hX : (s₁.gpr .r9).toNat + 2 ^ 64 * (s₁.gpr .r10).toNat + 2 ^ 128 * (s₂.gpr .r11).toNat +
        2 ^ 192 * (s₂.gpr .r12).toNat + 2 ^ 256 * (s₃.gpr .r13).toNat +
        2 ^ 256 * (2 ^ 64 * (s₃.gpr .r14).toNat) =
          (word s.mem base a).toNat * (word s.mem base (a + 8)).toNat +
          2 ^ 64 * ((word s.mem base a).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 128 * ((word s.mem base a).toNat * (word s.mem base (a + 24)).toNat) +
          2 ^ 128 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 192 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat) +
          2 ^ 256 * ((word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat) := by
      omega_using [e1, e2, e3]
    have hS : (s₅.gpr .r8).toNat + 2 ^ 64 * (s₅.gpr .r9).toNat + 2 ^ 128 * (s₆.gpr .r10).toNat +
        2 ^ 192 * (s₆.gpr .r11).toNat + 2 ^ 256 * (s₇.gpr .r12).toNat +
        2 ^ 256 * (2 ^ 64 * (s₇.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s₈.gpr .r14).toNat) +
        2 ^ 256 * (2 ^ 192 * (s₈.gpr .r15).toNat) + 2 ^ 256 * (2 ^ 256 * (s₈.gpr .rbp).toNat) =
          2 ^ 64 * (s₄.gpr .r9).toNat + 2 ^ 128 * (s₄.gpr .r10).toNat +
          2 ^ 192 * (s₄.gpr .r11).toNat + 2 ^ 256 * (s₄.gpr .r12).toNat +
          2 ^ 256 * (2 ^ 64 * (s₄.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s₄.gpr .r14).toNat) +
          2 ^ 256 * (2 ^ 192 * (s₄.gpr .r15).toNat) +
          (word s.mem base a).toNat * (word s.mem base a).toNat +
          2 ^ 128 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 8)).toNat) +
          2 ^ 256 * ((word s.mem base (a + 16)).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 256 * (2 ^ 128 * ((word s.mem base (a + 24)).toNat *
            (word s.mem base (a + 24)).toNat)) := by
      omega_using [e5, e6, e7, e8]
    have hD : 2 ^ 64 * (s₄.gpr .r9).toNat + 2 ^ 128 * (s₄.gpr .r10).toNat +
        2 ^ 192 * (s₄.gpr .r11).toNat + 2 ^ 256 * (s₄.gpr .r12).toNat +
        2 ^ 256 * (2 ^ 64 * (s₄.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s₄.gpr .r14).toNat) +
        2 ^ 256 * (2 ^ 192 * (s₄.gpr .r15).toNat) =
          2 * (2 ^ 64 * ((word s.mem base a).toNat * (word s.mem base (a + 8)).toNat) +
            2 ^ 128 * ((word s.mem base a).toNat * (word s.mem base (a + 16)).toNat) +
            2 ^ 192 * ((word s.mem base a).toNat * (word s.mem base (a + 24)).toNat) +
            2 ^ 192 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat) +
            2 ^ 256 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat) +
            2 ^ 256 * (2 ^ 64 * ((word s.mem base (a + 16)).toNat *
              (word s.mem base (a + 24)).toNat))) := by
      omega_using [e4, hX]
    have := (s₈.gpr .rbp).toNat.zero_le
    omega_using [hS, hD, hb]

end VG.Proof.X25519.X86_64

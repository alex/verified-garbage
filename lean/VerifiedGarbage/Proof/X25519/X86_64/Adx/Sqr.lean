import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul

/-!
# X25519 on x86-64: squaring with BMI2 and ADX

Untrusted: everything here is checked by Lean. `sqrX o a` in four phases:
the products `a₀ a_j`, `a₁ a_j` and `a₂ a₃` into `r9–r14` (`sqrA`–`sqrC`),
then those doubled while the squares `a_i²` are added (`sqrD`), and
reduced as in `mulX`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- `r ∉ [...]` and `a ≠ b` for literal registers. -/
local macro "nd" : tactic => `(tactic| decide)

theorem sqrA_eq (a : Nat) : sqrA a = ([.mov .rdx (.mem (sc a))] : List Instr) ++ (([clear] : List Instr) ++
    (([.mulx .r10 .r9 (.mem (sc (a + 8)))] : List Instr) ++ (mulAcc .r10 .r11 (.mem (sc (a + 16))) ++
      (mulAcc .r11 .r12 (.mem (sc (a + 24))) ++ ([.adcx .r12 (.reg .rbp)] : List Instr))))) := rfl

theorem sqrB_eq (a : Nat) : sqrB a = ([.mov .rdx (.mem (sc (a + 8)))] : List Instr) ++ (([clear] : List Instr) ++
    (madd .r11 .r12 (.mem (sc (a + 16))) ++ maddLast .r12 .r13 (.mem (sc (a + 24))))) := rfl

theorem sqrC_eq (a : Nat) : sqrC a = ([.mov .rdx (.mem (sc (a + 16)))] : List Instr) ++ (([clear] : List Instr) ++
    (mulAcc .r13 .r14 (.mem (sc (a + 24))) ++ ([.adcx .r14 (.reg .rbp)] : List Instr))) := rfl

theorem sqrD_eq (a : Nat) : sqrD a = ([clear] : List Instr) ++ (sqWord a .rax .r8 ++ (dblAdd .r9 .rax ++
    (sqWord (a + 8) .rcx .rax ++ (dblAdd .r10 .rax ++ (dblAdd .r11 .rcx ++
      (sqWord (a + 16) .rcx .rax ++ (dblAdd .r12 .rax ++ (dblAdd .r13 .rcx ++
        (sqWord (a + 24) .r15 .rax ++ (dblAdd .r14 .rax ++
          ([.adcx .r15 (.reg .rbp), .adox .r15 (.reg .rbp)] : List Instr))))))))))) := by
  simp only [sqrD, List.append_assoc]

theorem sqrX_eq (o a : Nat) :
    sqrX o a = sqrA a ++ (sqrB a ++ (sqrC a ++ (sqrD a ++ (reduceX ++ store4 o)))) := by
  simp only [sqrX, List.append_assoc]

/-- `r9–r12 = a₀ · (a₁, a₂, a₃)`. -/
theorem sqrA_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrA a)) s fun s' =>
      (s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat + 2 ^ 128 * (s'.gpr .r11).toNat +
          2 ^ 192 * (s'.gpr .r12).toNat =
        (word s.mem base a).toNat * (word s.mem base (a + 8)).toNat +
          2 ^ 64 * ((word s.mem base a).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 128 * ((word s.mem base a).toNat * (word s.mem base (a + 24)).toNat) ∧
      Keeps [.r9, .r10, .r11, .r12, .rax, .rdx, .rbp] s s' := by
  rw [sqrA_eq, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs (d := a) (by omega))) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, _, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s2 (readSrc_sc hs2 (by omega)) (noImm_mem _) (by nd))
    fun s3 ⟨e3, c3, _, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s3 (readSrc_sc hs3 (by omega)) (noImm_mem _) (c3.trans c2)
    (by nd) (by nd) (by nd)) fun s4 ⟨c4, hc4, _, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s4 (readSrc_sc hs4 (by omega)) (noImm_mem _) hc4
    (by nd) (by nd) (by nd)) fun s5 ⟨c5, hc5, _, e5, k5⟩ => ?_
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by nd), k4.1 _ (by nd), k3.1 _ (by nd), z2]
  refine WP.mono (carryC_ok s5 hc5 z5) fun s6 ⟨c6, _, _, e6, k6⟩ => ?_
  refine ⟨?_, (((((k1.mono (by nd)).trans (k2.mono (by nd))).trans (k3.mono (by nd))).trans
    (k4.mono (by nd))).trans (k5.mono (by nd))).trans (k6.mono (by nd))⟩
  have D2 : s2.gpr .rdx = word s.mem base a := (k2.1 _ (by nd)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base a := (k3.1 _ (by nd)).trans D2
  have D4 : s4.gpr .rdx = word s.mem base a := (k4.1 _ (by nd)).trans D3
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  rw [D2, M2] at e3
  rw [D3, M3] at e4
  rw [D4, M4] at e5
  have b1 : (word s.mem base a).toNat * ((word s.mem base (a + 8)).toNat +
      2 ^ 64 * (word s.mem base (a + 16)).toNat + 2 ^ 128 * (word s.mem base (a + 24)).toNat) ≤
        (2 ^ 64 - 1) * (2 ^ 192 - 1) := by
    have := (word s.mem base a).isLt; have := (word s.mem base (a + 8)).isLt
    have := (word s.mem base (a + 16)).isLt; have := (word s.mem base (a + 24)).isLt
    exact Nat.mul_le_mul (by omega) (by omega)
  simp only [Nat.mul_add, Nat.mul_left_comm (word s.mem base a).toNat] at b1
  rw [k6.1 .r9 (by nd), k5.1 .r9 (by nd), k4.1 .r9 (by nd), k6.1 .r10 (by nd),
    k5.1 .r10 (by nd), k6.1 .r11 (by nd)]
  simp only [Bool.toNat_false, Nat.add_zero] at e4
  have := Bool.toNat_le c6
  omega

/-- `r11–r13 += a₁ · (a₂, a₃)`. -/
theorem sqrB_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrB a)) s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .r12).toNat + 2 ^ 128 * (s'.gpr .r13).toNat =
        (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat +
          (word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat +
          2 ^ 64 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat) ∧
      Keeps [.r11, .r12, .r13, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [sqrB_eq, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs (d := a + 8) (by omega))) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s2 (readSrc_sc hs2 (by omega)) (noImm_mem _) c2 o2 (by nd) (by nd)
    (by nd) (by nd) (by nd)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nd)
  have z3 : s3.gpr .rbp = 0 := by rw [k3.1 _ (by nd), z2]
  refine WP.mono (maddLast_ok s3 (readSrc_sc hs3 (by omega)) (noImm_mem _) hc3 ho3 z3 (by nd)
    (by nd) (by nd) (by nd) (by nd)) fun s4 ⟨c4, o4, _, _, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by nd)).trans (k2.mono (by nd))).trans (k3.mono (by nd))).trans
    (k4.mono (by nd))⟩
  have D2 : s2.gpr .rdx = word s.mem base (a + 8) := (k2.1 _ (by nd)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base (a + 8) := (k3.1 _ (by nd)).trans D2
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  rw [D2, M2, k2.1 .r11 (by nd), k1.1 .r11 (by nd), k2.1 .r12 (by nd), k1.1 .r12 (by nd)] at e3
  rw [D3, M3] at e4
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  have b1 : (word s.mem base (a + 8)).toNat * ((word s.mem base (a + 16)).toNat +
      2 ^ 64 * (word s.mem base (a + 24)).toNat) ≤ (2 ^ 64 - 1) * (2 ^ 128 - 1) := by
    have := (word s.mem base (a + 8)).isLt; have := (word s.mem base (a + 16)).isLt
    have := (word s.mem base (a + 24)).isLt
    exact Nat.mul_le_mul (by omega) (by omega)
  simp only [Nat.mul_add, Nat.mul_left_comm (word s.mem base (a + 8)).toNat] at b1
  rw [k4.1 .r11 (by nd)]
  have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt
  have := Bool.toNat_le c4; have := Bool.toNat_le o4
  omega

/-- `r13–r14 += a₂ a₃`. -/
theorem sqrC_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrC a)) s fun s' =>
      (s'.gpr .r13).toNat + 2 ^ 64 * (s'.gpr .r14).toNat =
        (s.gpr .r13).toNat + (word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat ∧
      Keeps [.r13, .r14, .rax, .rdx, .rbp] s s' := by
  rw [sqrC_eq, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs (d := a + 16) (by omega))) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, _, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s2 (readSrc_sc hs2 (by omega)) (noImm_mem _) c2 (by nd) (by nd)
    (by nd)) fun s3 ⟨c3, hc3, _, e3, k3⟩ => ?_
  have z3 : s3.gpr .rbp = 0 := by rw [k3.1 _ (by nd), z2]
  refine WP.mono (carryC_ok s3 hc3 z3) fun s4 ⟨c4, _, _, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by nd)).trans (k2.mono (by nd))).trans (k3.mono (by nd))).trans
    (k4.mono (by nd))⟩
  have D2 : s2.gpr .rdx = word s.mem base (a + 16) := (k2.1 _ (by nd)).trans d1
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  rw [D2, M2, k2.1 .r13 (by nd), k1.1 .r13 (by nd)] at e3
  simp only [Bool.toNat_false, Nat.add_zero] at e3
  have b1 : (word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    have := (word s.mem base (a + 16)).isLt; have := (word s.mem base (a + 24)).isLt
    exact Nat.mul_le_mul (by omega) (by omega)
  rw [k4.1 .r13 (by nd)]
  have := (s.gpr .r13).isLt; have := Bool.toNat_le c4
  omega

/-- `hi:lo = [d]²`. -/
theorem sqWord_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096)
    {hi lo : Reg} (hhl : hi ≠ lo) :
    WP isa (.block (sqWord d hi lo)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        (word s.mem base d).toNat * (word s.mem base d).toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [.rdx, hi, lo] s s' := by
  rw [sqWord, show ([.mov .rdx (.mem (sc d)), .mulx hi lo (.reg .rdx)] : List Instr) =
    [.mov .rdx (.mem (sc d))] ++ [.mulx hi lo (.reg .rdx)] from rfl, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs hd)) fun s1 ⟨d1, c1, o1, k1⟩ => ?_
  refine WP.mono (mulx_ok s1 rfl (noImm_reg _) hhl) fun s2 ⟨e2, c2, o2, k2⟩ => ?_
  refine ⟨by rw [e2, d1], c2.trans c1, o2.trans o1, (k1.mono (by simp)).trans (k2.mono (by simp))⟩

/-- `r8–r15 = 2 · r9–r14 + Σ a_i²`, with a carry out `co`. -/
theorem sqrD_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrD a)) s fun s' => ∃ co : Nat,
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) +
          2 ^ 256 * val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) +
          2 ^ 256 * (2 ^ 256 * co) =
        2 * (2 ^ 64 * (s.gpr .r9).toNat + 2 ^ 128 * (s.gpr .r10).toNat +
          2 ^ 192 * (s.gpr .r11).toNat + 2 ^ 256 * (s.gpr .r12).toNat +
          2 ^ 256 * (2 ^ 64 * (s.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s.gpr .r14).toNat)) +
        (word s.mem base a).toNat * (word s.mem base a).toNat +
        2 ^ 128 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 8)).toNat) +
        2 ^ 256 * ((word s.mem base (a + 16)).toNat * (word s.mem base (a + 16)).toNat) +
        2 ^ 256 * (2 ^ 128 * ((word s.mem base (a + 24)).toNat * (word s.mem base (a + 24)).toNat)) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [sqrD_eq, WP.block_append_iff]
  refine WP.mono (clear_ok s) fun s1 ⟨z1, c1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (sqWord_ok hs1 (d := a) (by omega) (by nd)) fun s2 ⟨e2, c2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s2 (c2.trans c1) (o2.trans o1) (by nd))
    fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (sqWord_ok hs3 (d := a + 8) (by omega) (by nd)) fun s4 ⟨e4, c4, o4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s4 (c4.trans hc3) (o4.trans ho3) (by nd))
    fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s5 hc5 ho5 (by nd)) fun s6 ⟨c6, o6, hc6, ho6, e6, k6⟩ => ?_
  have hs6 := (hs4.of_keeps k5 (by nd)).of_keeps k6 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (sqWord_ok hs6 (d := a + 16) (by omega) (by nd)) fun s7 ⟨e7, c7, o7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s7 (c7.trans hc6) (o7.trans ho6) (by nd))
    fun s8 ⟨c8, o8, hc8, ho8, e8, k8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s8 hc8 ho8 (by nd)) fun s9 ⟨c9, o9, hc9, ho9, e9, k9⟩ => ?_
  have hs9 := (hs7.of_keeps k8 (by nd)).of_keeps k9 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (sqWord_ok hs9 (d := a + 24) (by omega) (by nd)) fun s10 ⟨e10, c10, o10, k10⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblAdd_ok s10 (c10.trans hc9) (o10.trans ho9) (by nd))
    fun s11 ⟨c11, o11, hc11, ho11, e11, k11⟩ => ?_
  have z11 : s11.gpr .rbp = 0 := by
    rw [k11.1 _ (by nd), k10.1 _ (by nd), k9.1 _ (by nd), k8.1 _ (by nd), k7.1 _ (by nd),
      k6.1 _ (by nd), k5.1 _ (by nd), k4.1 _ (by nd), k3.1 _ (by nd), k2.1 _ (by nd), z1]
  refine WP.mono (carries_ok s11 hc11 ho11 z11 (by nd)) fun s12 ⟨c12, o12, _, _, e12, k12⟩ => ?_
  refine ⟨c12.toNat + o12.toNat, ?_, ((((((((((((k1.mono (by nd)).trans (k2.mono (by nd))).trans
    (k3.mono (by nd))).trans (k4.mono (by nd))).trans (k5.mono (by nd))).trans
    (k6.mono (by nd))).trans (k7.mono (by nd))).trans (k8.mono (by nd))).trans
    (k9.mono (by nd))).trans (k10.mono (by nd))).trans (k11.mono (by nd))).trans
    (k12.mono (by nd)))⟩
  -- The memory the squares read, and the registers along the way.
  have M1 : s1.mem = s.mem := k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans (k2.2.1.trans M1)
  have M6 : s6.mem = s.mem := k6.2.1.trans (k5.2.1.trans (k4.2.1.trans M3))
  have M9 : s9.mem = s.mem := k9.2.1.trans (k8.2.1.trans (k7.2.1.trans M6))
  rw [M1] at e2
  rw [M3] at e4
  rw [M6] at e7
  rw [M9] at e10
  rw [k2.1 .r9 (by nd), k1.1 .r9 (by nd)] at e3
  rw [k4.1 .r10 (by nd), k3.1 .r10 (by nd), k2.1 .r10 (by nd), k1.1 .r10 (by nd)] at e5
  rw [k5.1 .rcx (by nd), k5.1 .r11 (by nd), k4.1 .r11 (by nd), k3.1 .r11 (by nd),
    k2.1 .r11 (by nd), k1.1 .r11 (by nd)] at e6
  rw [k7.1 .r12 (by nd), k6.1 .r12 (by nd), k5.1 .r12 (by nd), k4.1 .r12 (by nd),
    k3.1 .r12 (by nd), k2.1 .r12 (by nd), k1.1 .r12 (by nd)] at e8
  rw [k8.1 .rcx (by nd), k8.1 .r13 (by nd), k7.1 .r13 (by nd), k6.1 .r13 (by nd),
    k5.1 .r13 (by nd), k4.1 .r13 (by nd), k3.1 .r13 (by nd), k2.1 .r13 (by nd),
    k1.1 .r13 (by nd)] at e9
  rw [k10.1 .r14 (by nd), k9.1 .r14 (by nd), k8.1 .r14 (by nd), k7.1 .r14 (by nd),
    k6.1 .r14 (by nd), k5.1 .r14 (by nd), k4.1 .r14 (by nd), k3.1 .r14 (by nd),
    k2.1 .r14 (by nd), k1.1 .r14 (by nd)] at e11
  rw [k11.1 .r15 (by nd)] at e12
  simp only [Bool.toNat_false, Nat.add_zero] at e3
  simp only [val4]
  rw [k12.1 .r8 (by nd), k11.1 .r8 (by nd), k10.1 .r8 (by nd), k9.1 .r8 (by nd),
    k8.1 .r8 (by nd), k7.1 .r8 (by nd), k6.1 .r8 (by nd), k5.1 .r8 (by nd), k4.1 .r8 (by nd),
    k3.1 .r8 (by nd),
    k12.1 .r9 (by nd), k11.1 .r9 (by nd), k10.1 .r9 (by nd), k9.1 .r9 (by nd),
    k8.1 .r9 (by nd), k7.1 .r9 (by nd), k6.1 .r9 (by nd), k5.1 .r9 (by nd), k4.1 .r9 (by nd),
    k12.1 .r10 (by nd), k11.1 .r10 (by nd), k10.1 .r10 (by nd), k9.1 .r10 (by nd),
    k8.1 .r10 (by nd), k7.1 .r10 (by nd), k6.1 .r10 (by nd),
    k12.1 .r11 (by nd), k11.1 .r11 (by nd), k10.1 .r11 (by nd), k9.1 .r11 (by nd),
    k8.1 .r11 (by nd), k7.1 .r11 (by nd),
    k12.1 .r12 (by nd), k11.1 .r12 (by nd), k10.1 .r12 (by nd), k9.1 .r12 (by nd),
    k12.1 .r13 (by nd), k11.1 .r13 (by nd), k10.1 .r13 (by nd),
    k12.1 .r14 (by nd)]
  omega

/-- `[o] = [a]²`. -/
theorem sqrX_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqrX o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a := by
  rw [sqrX_eq, WP.block_append_iff]
  refine WP.mono (sqrA_ok hs ha) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (sqrB_ok hs₁ ha) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (sqrC_ok hs₂ ha) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (sqrD_ok hs₃ ha) fun s₄ ⟨co, e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by nd)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*]), k3.1 r (by simp [*]),
      k2.1 r (by simp [*]), k1.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5]
    congr 1
    -- Every phase read the same memory.
    rw [k1.2.1] at e2
    rw [k2.2.1, k1.2.1] at e3
    rw [k3.2.1, k2.2.1, k1.2.1] at e4
    -- The products into `r9–r14` along the way.
    rw [k3.1 .r9 (by nd), k2.1 .r9 (by nd), k3.1 .r10 (by nd), k2.1 .r10 (by nd),
      k3.1 .r11 (by nd), k3.1 .r12 (by nd)] at e4
    have hb : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
      Nat.mul_lt_mul'' (fe_lt _ _ _) (fe_lt _ _ _)
    simp only [X86_64.fe, val4, sq_words] at hb ⊢
    simp only [val4] at e4
    omega

end VG.Proof.X25519.X86_64

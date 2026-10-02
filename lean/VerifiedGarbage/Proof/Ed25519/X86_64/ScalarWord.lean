import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarStep

/-!
# Ed25519 scalar reduction: one word on x86-64

Untrusted. `wordFold` turns the remainder `r < L` and the next word `w` into
`l + L - h c` for `2^64 r + w = h 2^252 + l`, with `L = 2^252 + c`: below `2L`
and congruent to `2^64 r + w` modulo `L` (`fold_nat`). Each of its blocks is
checked against the numbers it computes.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps adc_carry add_carry sub_borrow sbb_borrow mulx_arith se0 toNat_ofBool
  chain_add chain_sub)
open VG.Spec.Ed25519 (L)

/-! ## Numbers -/

/-- `L - 2^252`. -/
def cL : Nat := 27742317777372353535851937790883648493

theorem L_eq : L = 2 ^ 252 + cL := by decide

theorem c_limbs : orderLo.toNat + 2 ^ 64 * orderHi.toNat = cL := by decide

/-- One word folded in: `l + L - h c` is below `2L` and congruent to `v = 2^64 r + w`. -/
theorem fold_nat (r w : Nat) (hr : r < L) (hw : w < 2 ^ 64) :
    (r * 2 ^ 64 + w) / 2 ^ 252 * cL < L ∧
    (r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * cL) < 2 * L ∧
    ((r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * cL)) % L = (r * 2 ^ 64 + w) % L := by
  rw [L_eq] at hr ⊢
  generalize hv : r * 2 ^ 64 + w = v
  have hv' : v < 2 ^ 317 := by rw [← hv]; simp only [cL] at hr; omega
  have hh : v / 2 ^ 252 < 2 ^ 65 := by omega
  have hc : v / 2 ^ 252 * cL < 2 ^ 65 * cL := Nat.mul_lt_mul_of_pos_right hh (by decide)
  have hd := Nat.div_add_mod v (2 ^ 252)
  simp only [cL] at hc ⊢
  refine ⟨by omega, by omega, ?_⟩
  generalize v / 2 ^ 252 = h at hc hd
  generalize v % 2 ^ 252 = l at hd ⊢
  subst hd
  have e : l + (2 ^ 252 + 27742317777372353535851937790883648493 - h * 27742317777372353535851937790883648493) +
      h * (2 ^ 252 + 27742317777372353535851937790883648493) =
      2 ^ 252 * h + l + (2 ^ 252 + 27742317777372353535851937790883648493) := by
    rw [Nat.mul_add]; omega
  rw [← Nat.add_mul_mod_self_right _ h, e, Nat.add_mod_right]

/-! ## The blocks -/

theorem or_mul16 {a b : Nat} (h : a < 2 ^ 4) : a ||| 16 * b = a + 16 * b := by
  rw [show 16 * b = b * 2 ^ 4 by omega, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm]

theorem sixteen (x : BitVec 64) :
    (x + x + (x + x) + (x + x + (x + x)) + (x + x + (x + x) + (x + x + (x + x)))).toNat =
      16 * (x.toNat % 2 ^ 60) := by
  have := x.isLt
  simp only [BitVec.toNat_add]
  omega

theorem foldPrep_ok (s : State) :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .rbp).toNat = (s.gpr .r10).toNat / 2 ^ 60 + 16 * ((s.gpr .r11).toNat % 2 ^ 60) ∧
      (t.gpr .r12).toNat = (s.gpr .r11).toNat / 2 ^ 60 ∧
      t.gpr .r8 = s.gpr .rax ∧ t.gpr .r9 = s.gpr .r8 ∧ t.gpr .r10 = s.gpr .r9 ∧
      (t.gpr .r11).toNat = (s.gpr .r10).toNat % 2 ^ 60 ∧
      Keeps [.rbp, .rcx, .r8, .r9, .r10, .r11, .r12] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    show 1 ≤ 60 ∧ 60 ≤ 63 by decide, and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, trivial, trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_or, sixteen, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact or_mul16 (by have := (s.gpr .r10).isLt; omega)
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rw [BitVec.toNat_and, show (1152921504606846975 : BitVec 64).toNat = 2 ^ 60 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem foldMul_ok (s : State) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .r13).toNat + 2 ^ 64 * (t.gpr .r14).toNat + 2 ^ 128 * (t.gpr .r15).toNat =
        (s.gpr .rbp).toNat * cL ∧ Keeps [.rax, .rcx, .rdx, .r13, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [foldMul, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have m1 := mulx_arith (s.gpr .rbp) orderLo
    have m2 := mulx_arith (s.gpr .rbp) orderHi
    have hc : (s.gpr .rbp).toNat * cL =
        (s.gpr .rbp).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .rbp).toNat * orderHi.toNat) := by
      rw [← c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have hb : (s.gpr .rbp).toNat * orderHi.toNat < 2 ^ 64 * 2 ^ 61 :=
      Nat.mul_lt_mul'' (s.gpr .rbp).isLt (by decide : orderHi.toNat < 2 ^ 61)
    have hz : (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat / 2 ^ 64)).toNat < 2 ^ 61 := by
      rw [BitVec.toNat_ofNat]; omega
    have ac := add_carry (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderLo.toNat / 2 ^ 64))
      (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat))
    have az := adc_carry (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat / 2 ^ 64)) 0
      (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderLo.toNat / 2 ^ 64)).toNat +
        (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat)).toNat))
    rw [hc]
    generalize (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderLo.toNat / 2 ^ 64)).toNat +
        (BitVec.ofNat 64 ((s.gpr .rbp).toNat * orderHi.toNat)).toNat)) = cy at ac az ⊢
    have hcy := Bool.toNat_le cy
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at az
    rw [decide_eq_false (by omega), Bool.toNat_false] at az
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem mask_and (h : BitVec 64) (hh : h.toNat ≤ 1) (v : BitVec 64) :
    (v &&& BitVec.setWidth 64 (0 : BitVec 32) - h).toNat = h.toNat * v.toNat := by
  rcases (by omega : h.toNat = 0 ∨ h.toNat = 1) with e | e
  · rw [show h = 0#64 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]
    simp
  · rw [show h = 1#64 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]
    simp only [show BitVec.setWidth 64 (0 : BitVec 32) - 1#64 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.toNat_ofNat]
    omega

theorem foldMask_ok (s : State) (h1 : (s.gpr .r12).toNat ≤ 1) (h15 : (s.gpr .r15).toNat < 2 ^ 62) :
    WP isa (.block foldMask) s fun t => t.gpr .r13 = s.gpr .r13 ∧
      (t.gpr .r14).toNat + 2 ^ 64 * (t.gpr .r15).toNat =
        (s.gpr .r14).toNat + 2 ^ 64 * (s.gpr .r15).toNat + (s.gpr .r12).toNat * cL ∧
      Keeps [.rax, .rcx, .rdx, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [foldMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have mx := mask_and (s.gpr .r12) h1 orderLo
    have my := mask_and (s.gpr .r12) h1 orderHi
    have hc : (s.gpr .r12).toNat * cL =
        (s.gpr .r12).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .r12).toNat * orderHi.toNat) := by
      rw [← c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have hH : orderHi.toNat < 2 ^ 61 := by decide
    have hy : (s.gpr .r12).toNat * orderHi.toNat < 2 ^ 61 := by
      rcases (by omega : (s.gpr .r12).toNat = 0 ∨ (s.gpr .r12).toNat = 1) with e | e <;> rw [e] <;> omega
    generalize orderLo &&& BitVec.setWidth 64 (0 : BitVec 32) - s.gpr .r12 = X at mx ⊢
    generalize orderHi &&& BitVec.setWidth 64 (0 : BitVec 32) - s.gpr .r12 = Y at my ⊢
    have ac := add_carry (s.gpr .r14) X
    generalize decide (2 ^ 64 ≤ (s.gpr .r14).toNat + X.toNat) = cy at ac ⊢
    have az := adc_carry (s.gpr .r15) Y cy
    have hcy := Bool.toNat_le cy
    rw [decide_eq_false (by omega), Bool.toNat_false] at az
    rw [hc]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

theorem eq_sub_of_chain {u T c : Nat} (hu : u < 2 ^ 256) (hT : T < L)
    (e : u + T = L + 2 ^ 256 * c) : u = L - T := by
  have := order_bound
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

theorem foldSub_ok (s : State)
    (ht : (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat + 2 ^ 128 * (s.gpr .r15).toNat < L) :
    WP isa (.block foldSub) s fun t =>
      val4 (t.gpr .rax) (t.gpr .rcx) (t.gpr .rdx) (t.gpr .rbp) =
        L - ((s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat + 2 ^ 128 * (s.gpr .r15).toNat) ∧
      Keeps [.rax, .rcx, .rdx, .rbp] s t := by
  apply WP.of_runBlock
  simp only [foldSub, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_sub orderLo orderHi (BitVec.setWidth 64 (0 : BitVec 32)) orderTop (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) 0
    simp only at e
    have hL : val4 orderLo orderHi (BitVec.setWidth 64 (0 : BitVec 32)) orderTop = L := by decide
    rw [hL] at e
    have hT : val4 (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) 0 =
        (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat + 2 ^ 128 * (s.gpr .r15).toNat := by
      simp only [val4, show (0 : BitVec 64).toNat = 0 from rfl]; omega
    rw [hT] at e
    exact eq_sub_of_chain (val4_bound _ _ _ _) ht e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem eq_of_chain {u x c : Nat} (hx : x < 2 ^ 256) (e : u + 2 ^ 256 * c = x) : u = x := by
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

theorem foldAdd_ok (s : State)
    (hs : scalarValue s + val4 (s.gpr .rax) (s.gpr .rcx) (s.gpr .rdx) (s.gpr .rbp) < 2 ^ 256) :
    WP isa (.block foldAdd) s fun t =>
      scalarValue t = scalarValue s + val4 (s.gpr .rax) (s.gpr .rcx) (s.gpr .rdx) (s.gpr .rbp) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [foldAdd, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) (s.gpr .rcx)
      (s.gpr .rdx) (s.gpr .rbp)
    simp only at e
    simp only [scalarValue, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    exact eq_of_chain hs e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The registers `wordFold` changes. -/
def foldClob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem wordFold_ok (s : State) (hr : scalarValue s < L) :
    WP isa (.block wordFold) s fun t => scalarValue t < 2 * L ∧
      scalarValue t % L = (scalarValue s * 2 ^ 64 + (s.gpr .rax).toNat) % L ∧ Keeps foldClob s t := by
  have hw := (s.gpr .rax).isLt
  obtain ⟨hlt, hlt2, hmod⟩ := fold_nat (scalarValue s) (s.gpr .rax).toNat hr hw
  have h0 := (s.gpr .r8).isLt; have h1 := (s.gpr .r9).isLt; have h2 := (s.gpr .r10).isLt
  have h3 : (s.gpr .r11).toNat < 2 ^ 61 := by
    have hL : L < 2 ^ 253 := by decide
    have := hr; simp only [scalarValue, val4] at this; omega
  -- `h` and `l` from the words
  have eh : (scalarValue s * 2 ^ 64 + (s.gpr .rax).toNat) / 2 ^ 252 =
      ((s.gpr .r10).toNat / 2 ^ 60 + 16 * ((s.gpr .r11).toNat % 2 ^ 60)) +
        2 ^ 64 * ((s.gpr .r11).toNat / 2 ^ 60) := by
    simp only [scalarValue, val4]; omega
  have el : (scalarValue s * 2 ^ 64 + (s.gpr .rax).toNat) % 2 ^ 252 =
      (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .r8).toNat + 2 ^ 128 * (s.gpr .r9).toNat +
        2 ^ 192 * ((s.gpr .r10).toNat % 2 ^ 60) := by
    simp only [scalarValue, val4]; omega
  rw [eh] at hlt hlt2 hmod
  rw [el] at hlt2 hmod
  simp only [wordFold, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (foldPrep_ok s) fun a ⟨abp, a12, a8, a9, a10, a11, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (foldMul_ok a) fun b ⟨bt, kb⟩ => ?_
  have b12 : (b.gpr .r12).toNat ≤ 1 := by
    rw [kb.1 _ (by decide), a12]; omega
  have b15 : (b.gpr .r15).toNat < 2 ^ 62 := by
    have : (a.gpr .rbp).toNat * cL < 2 ^ 64 * cL :=
      Nat.mul_lt_mul_of_pos_right (a.gpr .rbp).isLt (by decide)
    simp only [cL] at this bt; omega
  rw [WP.block_append_iff]
  refine WP.mono (foldMask_ok b b12 b15) fun c ⟨c13, ct, kc⟩ => ?_
  have hT : (c.gpr .r13).toNat + 2 ^ 64 * (c.gpr .r14).toNat + 2 ^ 128 * (c.gpr .r15).toNat =
      ((s.gpr .r10).toNat / 2 ^ 60 + 16 * ((s.gpr .r11).toNat % 2 ^ 60) +
        2 ^ 64 * ((s.gpr .r11).toNat / 2 ^ 60)) * cL := by
    have e12 : b.gpr .r12 = a.gpr .r12 := kb.1 _ (by decide)
    rw [c13, Nat.add_mul, ← abp, ← a12, ← e12, Nat.mul_assoc]
    omega
  rw [WP.block_append_iff]
  refine WP.mono (foldSub_ok c (by rw [hT]; exact hlt)) fun d ⟨du, kd⟩ => ?_
  have hl : scalarValue d = (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .r8).toNat + 2 ^ 128 * (s.gpr .r9).toNat +
      2 ^ 192 * ((s.gpr .r10).toNat % 2 ^ 60) := by
    simp only [scalarValue, val4]
    rw [kd.1 .r8 (by decide), kd.1 .r9 (by decide), kd.1 .r10 (by decide), kd.1 .r11 (by decide),
      kc.1 .r8 (by decide), kc.1 .r9 (by decide), kc.1 .r10 (by decide), kc.1 .r11 (by decide),
      kb.1 .r8 (by decide), kb.1 .r9 (by decide), kb.1 .r10 (by decide), kb.1 .r11 (by decide),
      a8, a9, a10, a11]
  rw [hT] at du
  refine WP.mono (foldAdd_ok d (by rw [hl, du]; have := order_bound; omega)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨by rw [tv, hl, du]; exact hlt2, by rw [tv, hl, du]; exact hmod, ?_⟩
  exact (((ka.mono (by simp [foldClob])).trans (kb.mono (by simp [foldClob]))).trans
    ((kc.mono (by simp [foldClob])).trans (kd.mono (by simp [foldClob])))).trans (kt.mono (by simp [foldClob]))

end VG.Proof.Ed25519.X86_64

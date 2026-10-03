import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.Framework.Range

/-!
# X448 on x86-64: the full reduction

`freeze a` leaves `[a] mod p` in `r8–r14`: `y = x + 1 + 2²²⁴` (a `fold` of
`r15 = 1`) carries out of 448 bits exactly when `x ≥ p`, and then
`y mod 2⁴⁴⁸ = x - p`, which the mask `r15 = -carry` selects word by word.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem sel_word (sw : Bool) (x y : BitVec 64) :
    ((y ^^^ x) &&& mask sw) ^^^ x = if sw then y else x := by
  cases sw
  · show (y ^^^ x) &&& 0#64 ^^^ x = x
    rw [BitVec.and_zero, BitVec.zero_xor]
  · simp only [mask, ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]

theorem w_ne_rax : ∀ i < 7, w i ≠ .rax := by decide
theorem w_ne_r15 : ∀ i < 7, w i ≠ .r15 := by decide
theorem w_mem : ∀ i < 7, w i ∈ W := by decide

/-- A word: `r = sw ? r : [d]`, with the mask in `r15`. -/
theorem selStep_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    {r : Reg} (hr : r ≠ .rax) (hr' : r ≠ .r15) {sw : Bool} (hm : s.gpr .r15 = mask sw) :
    WP isa (.block [.mov .rax (.mem (sc d)), .alu .xor r (.reg .rax),
      .alu .and r (.reg .r15), .alu .xor r (.reg .rax)]) s fun s' =>
      s'.gpr r = (if sw then s.gpr r else word s.mem base d) ∧
      KeepsR [.rax, r] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    load_sc hs hd, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hr'), RegUpd.gpr_arithFlags,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hr),
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.r15 = Reg.rax), RegUpd.mem_setReg,
    RegUpd.mem_arithFlags,
    Option.some.injEq, exists_eq_left', hm]
  refine ⟨sel_word _ _ _, ⟨fun r' hr'' => ?_, rfl, rfl⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr''.2, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setReg_of_ne _ _ hr''.1]

theorem w_inj : ∀ i < 7, ∀ j < 7, w i = w j → i = j := by decide

/-- The selection of every word. -/
theorem sel_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a + 56 ≤ 8192)
    {sw : Bool} (hm : s.gpr .r15 = mask sw) :
    WP isa (.block ((List.range 7).flatMap fun i =>
      [.mov .rax (.mem (sc (a + 8 * i))), .alu .xor (w i) (.reg .rax),
        .alu .and (w i) (.reg .r15), .alu .xor (w i) (.reg .rax)])) s fun s' =>
      (∀ i < 7, s'.gpr (w i) = if sw then s.gpr (w i) else word s.mem base (a + 8 * i)) ∧
      KeepsR (.rax :: W) s s' ∧ s'.mem = s.mem := by
  let inv := fun n (t : State) =>
    (∀ i < 7, t.gpr (w i) = if i < n then (if sw then s.gpr (w i) else word s.mem base (a + 8 * i))
      else s.gpr (w i)) ∧ KeepsR (.rax :: W) s t ∧ t.mem = s.mem
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block
      [.mov .rax (.mem (sc (a + 8 * n))), .alu .xor (w n) (.reg .rax),
        .alu .and (w n) (.reg .r15), .alu .xor (w n) (.reg .rax)]) t (inv (n + 1)) := by
    intro n t hn ⟨tw, tk, tm⟩
    have ht : Scr t base := hs.of_keepsR tk (by decide)
    have tr : t.gpr .r15 = mask sw := (tk.1 _ (by decide)).trans hm
    refine WP.mono (selStep_ok ht (d := a + 8 * n) (by omega) (w_ne_rax n hn) (w_ne_r15 n hn) tr)
      fun u ⟨uw, uk, um⟩ => ⟨fun i hi => ?_, ?_, um.trans tm⟩
    · by_cases h : i = n
      · subst h
        rw [uw, tw i hi, tm, ite_eq_right (Nat.lt_irrefl i), ite_eq_left (Nat.lt_succ_self i)]
      · have hne : w i ∉ [Reg.rax, w n] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨w_ne_rax i hi, fun e => h (w_inj i hi n hn e)⟩
        rw [uk.1 _ hne, tw i hi]
        by_cases h' : i < n
        · simp only [h', show i < n + 1 by omega, ite_true]
        · simp only [h', show ¬i < n + 1 by omega, ite_false]
    · refine tk.trans ⟨fun r hr => uk.1 r fun h => hr ?_, uk.2.1, uk.2.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (w_mem n hn)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) s
    ⟨fun i hi => by rw [ite_eq_right (by omega)], ⟨fun _ _ => rfl, rfl, rfl⟩, rfl⟩)
    fun t ⟨tw, tk, tm⟩ => ⟨fun i hi => by rw [tw i hi, ite_eq_left hi], tk, tm⟩

/-- `freeze a`: `r8–r14` hold `[a] mod p`. -/
theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (freeze a)) s fun s' =>
      rv s' W = fe s.mem base a % P ∧ Keeps (.rax :: .r15 :: W) s s' := by
  have ha' : a + 56 ≤ 1536 := ha
  simp only [freeze, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mov32_ok s .r15 1) fun s1 ⟨e1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs1 a W W_nodup (by decide) (by rw [W_len]; omega))
    fun s2 ⟨_, v2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have r15 : (s2.gpr .r15).toNat = 1 := by rw [k2.1 _ (by decide), e1]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok s2 (by rw [r15]; decide)) fun s3 ⟨c, hc, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .sbb .r15 (.reg .r15)]) s3 fun s' =>
      s'.gpr .r15 = mask c ∧ Keeps [.r15] s3 s' by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hc,
      Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq,
      exists_eq_left', BitVec.sub_self]
    refine ⟨by cases c <;> decide, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]) fun s4 ⟨m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  refine WP.mono (sel_ok hs4 (a := a) (by omega) m4) fun s5 ⟨w5, k5, mem5⟩ => ⟨?_, ?_⟩
  · have mm4 : s4.mem = s.mem := k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))
    rw [W_len, k1.2.1] at v2
    rw [v2, r15] at e3
    have w43 : rv s4 W = rv s3 W := k4.rv_eq (by decide)
    have hP := P_eq
    have hlt := fe_lt s.mem base a
    change rv s3 W + _ = fe s.mem base a + _ at e3
    cases c with
    | false =>
      have : rv s5 W = fe s.mem base a := by
        rw [rvW, fe, mv7]
        refine val7_congr fun i hi => ?_
        rw [w5 i hi]; simp only [Bool.false_eq_true, ite_false, mm4]
      rw [this, Nat.mod_eq_of_lt]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e3
      have := rv_lt s3 W; rw [len_W] at this
      omega
    | true =>
      have : rv s5 W = rv s3 W := by
        rw [rvW, rvW]
        refine val7_congr fun i hi => ?_
        rw [w5 i hi, ite_eq_left rfl, k4.1 _ (by simp [w_ne_r15 i hi])]
      simp only [Bool.toNat_true, Nat.mul_one] at e3
      rw [this, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [k5.1 r (by simp [hr.1, hr.2.2]), k4.1 r (by simp [hr.2.1]),
        k3.1 r (by simp [hr.1, hr.2.2]), k2.1 r hr.2.2, k1.1 r (by simp [hr.2.1])]
    · rw [mem5, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
    · rw [k5.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
    · rw [k5.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]

end VG.Proof.X448.X86_64

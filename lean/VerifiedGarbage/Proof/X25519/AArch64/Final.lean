import VerifiedGarbage.Proof.X25519.AArch64.Invert
import VerifiedGarbage.Proof.X25519.AArch64.Codec

/-!
# X25519 on AArch64: the full reduction and the result

Untrusted: everything here is checked by Lean. `finish`: the product
`x2 · z2^(p-2)`, loaded into the limb registers, reduced fully (`freeze`),
packed into four words at `out` (`pack`), and our caller's registers
restored.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Loading the limbs -/

theorem loads_ok {b : Addr} {a : Nat} (ha : Slot a) :
    ∀ n ≤ 15, ∀ s : State, Sc b s →
    WP isa (.block ((List.range n).map fun k => ld (dreg k) (a + 8 * k))) s fun s' =>
      (∀ k < n, v s' (dreg k) = wd s.mem b (a + 8 * k)) ∧ Kp DR s s' ∧ s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (loads_ok ha n (by omega) s hs) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    refine WP.block_cons_iff.mpr ⟨_, exec_ld hs₁ _ (ha.off (i := n) (by omega)), WP.block_nil
      ⟨fun k hk => ?_, (k₁.trans (kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by
        simp only [List.cons_subset, List.nil_subset, and_true]; exact dreg_mem n (by omega)⟩), by
        rw [mem_wx, m₁]⟩⟩
    by_cases hkn : k = n
    · subst hkn; rw [v, gpr_wx_self, wd_def, m₁]
    · rw [v, gpr_wx_ne _ _ (dreg_ne (by omega) (by omega) hkn)]; exact e₁ k (by omega)

theorem load_ok {b : Addr} {s : State} (hs : Sc b s) {a : Nat} (ha : Slot a) :
    WP isa (.block (load a)) s fun s' => regs s' = limbs s.mem b a ∧ Kp DR s s' ∧ s'.mem = s.mem :=
  WP.mono (loads_ok ha 15 (by decide) s hs) fun s' ⟨e, k, m⟩ => ⟨funext fun i => by
    simp only [regs, limbs]; split
    · rename_i hi; exact e i hi
    · rfl, k, m⟩

/-! ## The full reduction -/

theorem quotN_ok : ∀ n ≤ 14, ∀ s : State,
    WP isa (.block (([.addImm .x .x17 (dreg 0) 19, .lsr .x .x17 .x17 17] : List Instr) ++
      (List.range n).flatMap fun k => [.add .x .x17 (dreg (k + 1)) .x17, .lsr .x .x17 .x17 17])) s
      fun s' => v s' .x17 = quotN (regs s) n ∧ Kp [.x17] s s' ∧ s'.mem = s.mem
  | 0, _, s => by
    apply WP.of_runBlock
    simp only [List.range_zero, List.flatMap_nil, List.append_nil, runBlock_cons,
      exec_addImm_x (show 19 < 4096 by decide), runStep_some, exec_lsr (show 17 < 64 by decide), read_x,
      gpr_wx_self, runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ((kp_wx s _ _).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩
    rw [v, gpr_wx_self, lsr_toNat, BitVec.toNat_add, quotN, regs, ite_eq_left (by decide)]; rfl
  | n + 1, hn, s => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc]
    refine WP.block_append (WP.mono (quotN_ok n (by omega) s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    obtain ⟨d17, -⟩ := dreg_facts (n + 1) (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add_x, runStep_some, exec_lsr (show 17 < 64 by decide),
      gpr_wx_self, runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ((k₁.trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).sub (by sub_regs), by rw [mem_wx, mem_wx, m₁]⟩
    rw [v, gpr_wx_self, lsr_toNat, BitVec.toNat_add, quotN, show (s₁.gpr .x17).toNat = _ from e₁,
      show (s₁.gpr (dreg (n + 1))).toNat = regs s (n + 1) by
        rw [regs, ite_eq_left (by omega), v, k₁.gpr _ (by simpa using d17)]]

theorem add19_ok {s : State} (h19 : s.gpr .x21 = 19) :
    WP isa (.block [.madd .x (dreg 0) .x17 .x21 (dreg 0)]) s fun s' =>
      regs s' = add19 (regs s) (v s .x17) ∧ Kp DR s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, -, -, d21, -⟩ := dreg_facts 0 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_madd_x, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, (kp_wx s _ _).sub (by
    simp only [List.cons_subset, List.nil_subset, and_true]; exact dreg_mem 0 (by decide)), rfl⟩
  simp only [regs, add19]
  by_cases hi : i < 15
  · simp only [hi, ite_true]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_left rfl, v, gpr_wx_self, madd_toNat, h19, ite_eq_left (by decide)]; rfl
    · rw [ite_eq_right h0, v, gpr_wx_ne _ _ (dreg_ne hi (by decide) h0)]
  · simp only [hi, ite_false, show i ≠ 0 by omega]

theorem maskTop_ok {s : State} (hm : s.gpr .x22 = 0x1ffff) :
    WP isa (.block [.logic .and .x (dreg 14) (dreg 14) .x22]) s fun s' =>
      regs s' = maskTop (regs s) ∧ Kp DR s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_and_x, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, (kp_wx s _ _).sub (by
    simp only [List.cons_subset, List.nil_subset, and_true]; exact dreg_mem 14 (by decide)), rfl⟩
  simp only [regs, maskTop]
  by_cases hi : i < 15
  · simp only [hi, ite_true]
    by_cases h14 : i = 14
    · subst h14
      rw [ite_eq_left rfl, v, gpr_wx_self, and_mask17 _ _ hm, ite_eq_left (by decide)]
    · rw [ite_eq_right h14, v, gpr_wx_ne _ _ (dreg_ne hi (by decide) h14)]
  · simp only [hi, ite_false, show i ≠ 14 by omega]

theorem kp_field {W : List Reg} {s s' : State} (h : Kp W s s') (hW : W ⊆ fieldRegs) : Kp fieldRegs s s' :=
  h.sub hW

theorem DR_sub : DR ⊆ fieldRegs := fun _ h => List.mem_append_left _ (List.mem_append_left _ h)

/-- `freeze`: the limb registers reduced fully. -/
theorem freeze_ok (s : State) :
    WP isa (.block freeze) s fun s' => regs s' = freezeF (regs s) ∧ Kp fieldRegs s s' ∧ s'.mem = s.mem := by
  simp only [freeze, List.append_assoc]
  refine WP.block_append (WP.mono (mask17_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (const19_ok s₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hm₂ : s₂.gpr .x22 = 0x1ffff := by rw [k₂.gpr _ (by decide), e₁]
  have r₂ : regs s₂ = regs s := funext fun i => by
    simp only [regs]; split
    · rename_i hi
      obtain ⟨-, -, -, d21, d22, -⟩ := dreg_facts i hi
      rw [v, k₂.gpr _ (by simpa using d21), k₁.gpr _ (by simpa using d22)]
    · rfl
  refine WP.block_append (WP.mono (chain_ok 14 (by decide) s₂ hm₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hm₃ : s₃.gpr .x22 = 0x1ffff := by rw [k₃.gpr _ (by decide), hm₂]
  have h19₃ : s₃.gpr .x21 = 19 := by rw [k₃.gpr _ (by decide), e₂]
  refine WP.block_append (WP.mono (foldTop_ok hm₃ h19₃) fun s₄ ⟨e₄, k₄, m₄⟩ => ?_)
  have hm₄ : s₄.gpr .x22 = 0x1ffff := by rw [k₄.gpr _ (by decide), hm₃]
  have h19₄ : s₄.gpr .x21 = 19 := by rw [k₄.gpr _ (by decide), h19₃]
  refine WP.block_append (WP.mono (chain_ok 14 (by decide) s₄ hm₄) fun s₅ ⟨e₅, k₅, m₅⟩ => ?_)
  have hm₅ : s₅.gpr .x22 = 0x1ffff := by rw [k₅.gpr _ (by decide), hm₄]
  have h19₅ : s₅.gpr .x21 = 19 := by rw [k₅.gpr _ (by decide), h19₄]
  refine WP.block_append (WP.mono (foldTop_ok hm₅ h19₅) fun s₆ ⟨e₆, k₆, m₆⟩ => ?_)
  have hm₆ : s₆.gpr .x22 = 0x1ffff := by rw [k₆.gpr _ (by decide), hm₅]
  have h19₆ : s₆.gpr .x21 = 19 := by rw [k₆.gpr _ (by decide), h19₅]
  refine WP.block_append (WP.mono (quotN_ok 14 (by decide) s₆ : WP isa (.block quot) s₆ _)
    fun s₇ ⟨e₇, k₇, m₇⟩ => ?_)
  have hm₇ : s₇.gpr .x22 = 0x1ffff := by rw [k₇.gpr _ (by decide), hm₆]
  have h19₇ : s₇.gpr .x21 = 19 := by rw [k₇.gpr _ (by decide), h19₆]
  have r₇ : regs s₇ = regs s₆ := funext fun i => by
    simp only [regs]; split
    · rename_i hi
      obtain ⟨d17, -⟩ := dreg_facts i hi
      rw [v, k₇.gpr _ (by simpa using d17)]
    · rfl
  refine WP.block_append (WP.mono (add19_ok h19₇) fun s₈ ⟨e₈, k₈, m₈⟩ => ?_)
  have hm₈ : s₈.gpr .x22 = 0x1ffff := by rw [k₈.gpr _ (by decide), hm₇]
  refine WP.block_append (WP.mono (chain_ok 14 (by decide) s₈ hm₈) fun s₉ ⟨e₉, k₉, m₉⟩ => ?_)
  have hm₉ : s₉.gpr .x22 = 0x1ffff := by rw [k₉.gpr _ (by decide), hm₈]
  refine WP.mono (maskTop_ok hm₉) fun s₁₀ ⟨e₁₀, k₁₀, m₁₀⟩ => ⟨?_, ?_, ?_⟩
  · rw [e₁₀, e₉, e₈, e₇, r₇, e₆, e₅, e₄, e₃, r₂]; rfl
  · exact (((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans
      k₉).trans k₁₀).sub (by decide)
  · rw [m₁₀, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]

/-! ## Packing -/

theorem regs_kp {s s' : State} {W : List Reg} (h : Kp W s s') (hW : ∀ k < 15, dreg k ∉ W) : regs s' = regs s :=
  funext fun i => by
    simp only [regs]; split
    · rename_i hi; rw [v, h.gpr _ (hW i hi)]
    · rfl

theorem place_ok {s : State} {t : Reg} {i j : Nat} (hi : i < 15) (hw : 64 * j < 17 * i + 17 ∧ 17 * i < 64 * j + 64) :
    WP isa (.block [place t i j]) s fun s' => v s' t = placeV (regs s) i j ∧ Kp [t] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [place, placeV, regs, hi, ite_true]
  split
  · simp only [runBlock_cons, exec_lsl (show 17 * i - 64 * j < 64 by omega), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left', v, gpr_wx_self, lsl_toNat]
    exact ⟨trivial, kp_wx s _ _, rfl⟩
  · simp only [runBlock_cons, exec_lsr (show 64 * j - 17 * i < 64 by omega), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left', v, gpr_wx_self, lsr_toNat]
    exact ⟨trivial, kp_wx s _ _, rfl⟩

theorem accs_ok {j : Nat} : ∀ (is : List Nat), (∀ i ∈ is, i < 15 ∧ 64 * j < 17 * i + 17 ∧ 17 * i < 64 * j + 64) →
    ∀ s : State, WP isa (.block (is.flatMap fun i => [place .x19 i j, .add .x .x17 .x17 .x19])) s fun s' =>
      v s' .x17 = is.foldl (fun acc i => (acc + placeV (regs s) i j) % 2 ^ 64) (v s .x17) ∧
      Kp [.x17, .x19] s s' ∧ s'.mem = s.mem
  | [], _, s => WP.block_nil ⟨rfl, Kp.refl _ _, rfl⟩
  | i :: is, h, s => by
    obtain ⟨hi, hw⟩ := h i List.mem_cons_self
    rw [List.flatMap_cons, show [place .x19 i j, .add .x .x17 .x17 .x19] =
      [place .x19 i j] ++ ([.add .x .x17 .x17 .x19] : List Instr) from rfl, List.append_assoc]
    refine WP.block_append (WP.mono (place_ok (t := .x19) hi hw) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    refine WP.block_cons_iff.mpr ⟨_, exec_add_x, ?_⟩
    have r₂ : regs (s₁.write .x .x17 (s₁.gpr .x17 + s₁.gpr .x19)) = regs s :=
      (regs_kp ((k₁.trans (kp_wx _ _ _))) fun k hk => by
        obtain ⟨d17, d19, -⟩ := dreg_facts k hk
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨d19, d17⟩)
    refine WP.mono (accs_ok is (fun i hi => h i (List.mem_cons_of_mem _ hi)) _) fun s₃ ⟨e₃, k₃, m₃⟩ =>
      ⟨?_, ((k₁.trans (kp_wx _ _ _)).trans k₃).sub (by sub_regs), by rw [m₃, mem_wx, m₁]⟩
    rw [e₃, r₂, List.foldl_cons, v, gpr_wx_self, BitVec.toNat_add, ← v, ← v, e₁,
      show v s₁ .x17 = v s .x17 by rw [v, v, k₁.gpr _ (by decide)]]

theorem wordLimbs_facts : ∀ j < 4, ∀ i ∈ wordLimbs j, i < 15 ∧ 64 * j < 17 * i + 17 ∧ 17 * i < 64 * j + 64 := by
  decide

theorem wordLimbs_ne : ∀ j < 4, wordLimbs j ≠ [] := by decide

/-- The output region. -/
abbrev outR (o : Addr) : Region := ⟨o, 32⟩

theorem packWord_ok {o : Addr} {s : State} (hx0 : s.gpr .x0 = o) (hw : outR o ∈ s.wr) {j : Nat} (hj : j < 4) :
    WP isa (.block (packWord j)) s fun s' =>
      ∃ x : BitVec 64, x.toNat = packV (regs s) j ∧ s'.mem = s.mem.writeW (o + BitVec.ofNat 64 (8 * j)) x ∧
      Kp [.x17, .x19] s s' := by
  have hf := wordLimbs_facts j hj
  obtain ⟨i, is, h⟩ : ∃ i is, wordLimbs j = i :: is := by
    cases hw : wordLimbs j with
    | nil => exact absurd hw (wordLimbs_ne j hj)
    | cons i is => exact ⟨i, is, rfl⟩
  simp only [packWord, packV, h]
  · rw [h] at hf
    obtain ⟨hi, hw'⟩ := hf i List.mem_cons_self
    rw [List.cons_append, show ∀ l : List Instr, place .x17 i j :: l = [place .x17 i j] ++ l from fun _ => rfl]
    refine WP.block_append (WP.mono (place_ok (t := .x17) hi hw') fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    refine WP.block_append (WP.mono (accs_ok is (fun i hi => hf i (List.mem_cons_of_mem _ hi)) s₁)
      fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
    have hx0₂ : s₂.gpr .x0 = o := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hx0]
    have hin : InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 (8 * j)) 8 :=
      ⟨outR o, by rw [k₂.wr, k₁.wr]; exact hw, by rw [hx0₂]; exact Offset.contains_base o (by omega) (by omega)⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_str_x ⟨by omega, by omega⟩ hin, WP.block_nil ⟨s₂.gpr .x17, ?_, ?_, ?_⟩⟩
    · have r₁ : regs s₁ = regs s := regs_kp k₁ fun k hk => by
        obtain ⟨d17, -⟩ := dreg_facts k hk; simpa using d17
      rw [← v, e₂, e₁, r₁]
    · rw [hx0₂, m₂, m₁]
    · exact ⟨fun r hr => (k₁.trans k₂).gpr r (by simp only [List.mem_append]; exact fun h => hr (by
        rcases h with h | h <;> simp_all)), (k₁.trans k₂).rd, (k₁.trans k₂).wr⟩

end VG.Proof.X25519.AArch64

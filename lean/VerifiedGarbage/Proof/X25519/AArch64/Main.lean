import VerifiedGarbage.Proof.X25519.AArch64.Setup

/-!
# X25519 on AArch64: the whole function
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## The swap after the ladder -/

theorem lastSwap_ok {b : Addr} {s : State} {x1 : Fe} {st : Ladder} (hs : Sc b s)
    (hsl : Sl s.mem b (lvals x1 st) lbnds) (hsw : st.swap ≤ 1) (h24 : s.gpr .x24 = BitVec.ofNat 64 st.swap) :
    WP isa (.block lastSwap) s fun s' => Sc b s' ∧ (∃ vals, Sl s'.mem b vals lbnds ∧
      vals 1 = (cswap st.swap st.x2 st.x3).1 ∧ vals 2 = (cswap st.swap st.z2 st.z3).1) ∧
      Kp fieldRegs s s' ∧ Frame [slotArea b] s.mem s'.mem := by
  have e : lastSwap = ([.addImm .x .x20 .x24 0] ++ maskOf) ++
      (Impl.X25519.AArch64.cswap (slot 1) (slot 3) ++ Impl.X25519.AArch64.cswap (slot 2) (slot 4)) := by
    simp only [lastSwap, List.append_assoc, X2, X3, Z2, Z3]
  rw [e]
  have h1 : WP isa (.block ([.addImm .x .x20 .x24 0] ++ maskOf)) s fun s₁ =>
      s₁.gpr .x22 = maskB (st.swap == 1) ∧ Kp [.x20, .x22] s s₁ ∧ s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [maskOf, List.cons_append, List.nil_append, runBlock_cons, exec_addImm_x (show 0 < 4096 by decide),
      runStep_some, exec_movz, exec_sub_x, read_x, runBlock_nil, Option.some.injEq, exists_eq_left',
      gpr_wx_self, gpr_wx_ne _ _ (show Reg.x20 ≠ .x22 by decide), h24, BitVec.add_zero]
    refine ⟨?_, (((kp_wx s _ _).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩
    rw [show BitVec.setWidth 64 (0 : BitVec 16) = 0 from rfl, maskB_of hsw]
  refine WP.block_append (WP.mono h1 fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have hI : Inv b s₁ s₁ (lvals x1 st) lbnds := Inv.of_sl (hs.of_kp k₁ (by decide)) (by rw [m₁]; exact hsl)
  refine WP.block_append (WP.mono (cswap_inv hI (x := 1) (y := 3) (by decide) (by decide) (by decide)
    (k := 18) rfl rfl e₁) fun s₂ ⟨h₂, g₂⟩ => ?_)
  refine WP.mono (cswap_inv h₂ (x := 2) (y := 4) (by decide) (by decide) (by decide)
    (k := 18) (sw := st.swap) rfl rfl (by rw [g₂, e₁])) fun s₃ ⟨h₃, _⟩ => ⟨h₃.sc, ⟨_, h₃.sl, ?_, ?_⟩, (k₁.trans h₃.kp).sub
      (List.append_subset.mpr ⟨by decide, List.Subset.refl _⟩), by rw [← m₁]; exact h₃.fr⟩
  · simp only [Function.update_apply, lvals, ite_true, ite_false, Nat.reduceEqDiff]
  · simp only [Function.update_apply, lvals, ite_true, ite_false, Nat.reduceEqDiff]

/-! ## The initial values -/

theorem initSlots_ok {b : Addr} {s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat} (hs : Sc b s)
    (hsl : Sl s.mem b vals bnds) {x1 : Fe} (h0 : vals 0 = x1) (h3 : vals 3 = x1) (hb0 : bnds 0 = some 18)
    (hb3 : bnds 3 = some 18) :
    WP isa (.block initSlots) s fun s' => Sc b s' ∧ Sl s'.mem b (lvals x1 (init x1)) lbnds ∧
      Kp fieldRegs s s' ∧ Frame [slotArea b] s.mem s'.mem := by
  have e : initSlots = [.movz .x .x17 0 0] ++ (zero (slot 2) ++ ((zero (slot 1) ++ [.movz .x .x19 1 0, st .x19 (slot 1)])
      ++ copy (slot 4) (slot 1))) := by
    simp only [initSlots, List.append_assoc, X2, Z2, Z3]
  rw [e, List.singleton_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
  have hI : Inv b (s.write .x .x17 ((0 : BitVec 16).setWidth 64)) (s.write .x .x17 ((0 : BitVec 16).setWidth 64))
      vals bnds := Inv.of_sl (sc_wx _ _ hs (by decide)) (by rw [mem_wx]; exact hsl)
  refine WP.block_append (WP.mono (zero_inv hI (o := 2) (by decide) (gpr_wx_self _ _ _)) fun s₁ ⟨h₁, k₁⟩ => ?_)
  have g17 : s₁.gpr .x17 = 0 := by
    rw [k₁.gpr _ (by simp), gpr_wx_self]; rfl
  refine WP.block_append (WP.mono (one_inv h₁ (o := 1) (by decide) g17) fun s₂ h₂ => ?_)
  refine WP.mono (copy_inv h₂ (o := 4) (a := 1) (by decide) (by decide) (ka := 18) (by simp)) fun s₃ h₃ =>
    ⟨h₃.sc, h₃.sl.weaken fun n hn j hj => ?_, ((kp_wx _ _ _).trans h₃.kp).sub (List.append_subset.mpr
      ⟨by decide, List.Subset.refl _⟩), by rw [← mem_wx s .x17 ((0 : BitVec 16).setWidth 64)]; exact h₃.fr⟩
  simp only [lbnds] at hj
  split at hj
  · cases hj
    rename_i h5
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp [lvals, init, h0, h3, hb0, hb3]
  · cases hj

/-! ## Packing and restoring -/

theorem packN_ok {o : Addr} : ∀ n ≤ 4, ∀ s : State, s.gpr .x0 = o → outR o ∈ s.wr →
    WP isa (.block ((List.range n).flatMap packWord)) s fun s' =>
      (∀ j < n, (s'.mem.readW (o + BitVec.ofNat 64 (8 * j)) 64).toNat = packV (regs s) j) ∧
      Frame [outR o] s.mem s'.mem ∧ Kp [.x17, .x19] s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun j hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hx0, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (packN_ok n (by omega) s hx0 hw) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have r₁ : regs s₁ = regs s := regs_kp k₁ fun k hk => by
      obtain ⟨d17, d19, -⟩ := dreg_facts k hk; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨d17, d19⟩
    refine WP.mono (packWord_ok (o := o) (by rw [k₁.gpr _ (by decide), hx0]) (by rw [k₁.wr]; exact hw) (j := n) (by omega))
      fun s₂ ⟨x, hx, m₂, k₂⟩ => ⟨fun j hj => ?_, ?_, (k₁.trans k₂).sub (by sub_regs)⟩
    · rw [m₂]
      by_cases hjn : j = n
      · subst hjn; rw [Mem.readW_writeW_self64, hx, r₁]
      · rw [Mem.readW_writeW_sep (Offset.sep o (by omega) (by omega) (by omega)) (by decide)]
        exact e₁ j (by omega)
    · rw [m₂]
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base o (by omega) (by omega))

theorem saved_mem : ∀ n < 6, saved.getD n .x19 ∈ saved := by decide

theorem saved_ne : ∀ k < 6, ∀ n < 6, k ≠ n → saved.getD k .x19 ≠ saved.getD n .x19 := by decide

theorem restoreN_ok {b : Addr} : ∀ n ≤ 6, ∀ s : State, Sc b s →
    WP isa (.block ((List.range n).map fun k => ld (saved.getD k .x19) (SAVE + 8 * k))) s fun s' =>
      (∀ k < n, s'.gpr (saved.getD k .x19) = s.mem.readW (b + BitVec.ofNat 64 (SAVE + 8 * k)) 64) ∧
      Kp saved s s' ∧ s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (restoreN_ok n (by omega) s hs) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have ho : Off (SAVE + 8 * n) := ⟨by simp only [SAVE]; omega, by simp only [SAVE]; omega⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_ld hs₁ _ ho, WP.block_nil ⟨fun k hk => ?_,
      (k₁.trans (kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by
        simp only [List.cons_subset, List.nil_subset, and_true]; exact saved_mem n (by omega)⟩),
        by rw [mem_wx, m₁]⟩⟩
    by_cases hkn : k = n
    · subst hkn; rw [gpr_wx_self, m₁]
    · rw [gpr_wx_ne _ _ (saved_ne k (by omega) n (by omega) hkn)]; exact e₁ k (by omega)

/-! ## The end -/

theorem finish_ok {b o : Addr} {s : State} (hs : Sc b s) {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (hsl : Sl s.mem b vals bnds) (h1 : bnds 1 = some 18) (h14 : bnds 14 = some 18)
    (hx0 : s.gpr .x0 = o) (hw : outR o ∈ s.wr) (hdo : (saveR b).Disjoint (outR o)) :
    WP isa (.block finish) s fun s' =>
      bytesAt s'.mem o 32 = leBytes 32 (vals 1 * vals 14).val ∧
      (∀ k < 6, s'.gpr (saved.getD k .x19) =
        (s.mem.readW (b + BitVec.ofNat 64 (SAVE + 8 * k)) 64)) ∧
      Kp (fieldRegs ++ saved) s s' ∧ Frame [slotArea b, outR o] s.mem s'.mem := by
  rw [finish, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (mul_inv (Inv.of_sl hs hsl) (o := 1) (a := 1) (c := 14) (by decide)
    (by decide) (by decide) h1 h14 (by decide) (by decide)) fun s₁ h₁ => ?_)
  obtain ⟨rb, rv⟩ := h₁.sl 1 (by decide) 18 (by simp)
  simp only [Function.update_self] at rv
  refine WP.block_append (WP.mono (load_ok h₁.sc (slot_ok (n := 1) (by decide))) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  refine WP.block_append (WP.mono (freeze_ok s₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hx0₃ : s₃.gpr .x0 = o := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), h₁.kp.gpr _ (by decide), hx0]
  have hw₃ : outR o ∈ s₃.wr := by rw [k₃.wr, k₂.wr, h₁.kp.wr]; exact hw
  refine WP.block_append (WP.mono (packN_ok 4 (by decide) s₃ hx0₃ hw₃) fun s₄ ⟨e₄, f₄, k₄⟩ => ?_)
  have hs₄ : Sc b s₄ := ((h₁.sc.of_kp k₂ (by decide)).of_kp k₃ (by decide)).of_kp k₄ (by decide)
  refine WP.mono (restoreN_ok 6 (by decide) s₄ hs₄) fun s₅ ⟨e₅, k₅, m₅⟩ => ⟨?_, fun k hk => ?_, ?_, ?_⟩
  · -- the result
    have fz := freezeF_spec (f := limbs s₁.mem b (slot 1)) rb
    have hX2 : X2 = slot 1 := rfl
    rw [hX2] at e₂
    rw [← e₂, ← e₃] at fz
    obtain ⟨fb, flt, fv⟩ := fz
    have hp := packV_eq fb
    have hV : (vals 1 * vals 14).val = valN (regs s₃) 15 := by
      rw [← rv, ← e₂, ← fv, toFe_val]
      exact Nat.mod_eq_of_lt flt
    rw [m₅, hV]
    refine bytesAt_leBytes_words64 _ _ _ ?_ ?_ ?_ ?_
    · have := e₄ 0 (by decide); rw [hp 0 (by decide)] at this
      simpa using this
    · have := e₄ 1 (by decide); rw [hp 1 (by decide)] at this; exact this
    · have := e₄ 2 (by decide); rw [hp 2 (by decide)] at this; exact this
    · have := e₄ 3 (by decide); rw [hp 3 (by decide)] at this; exact this
  · -- the saved registers
    have hc : (saveR b).Contains (b + BitVec.ofNat 64 (SAVE + 8 * k)) (64 / 8) :=
      Offset.contains_base b (by simp only [SAVE]; omega) (by simp only [SAVE]; omega)
    rw [e₅ k hk, f₄.readW hc (by simpa using hdo) (by decide), m₃, m₂,
      h₁.fr.readW hc (by simpa using Offset.base_disjoint b (k := 48) (e := 64) (n := 1920) (by decide) (by decide))
        (by decide)]
  · exact ((((h₁.kp.trans k₂).trans k₃).trans k₄).trans k₅).sub (by decide)
  · have f₁ : Frame [slotArea b, outR o] s.mem s₁.mem := h₁.fr.mono (by simp)
    have f₄' : Frame [slotArea b, outR o] s₃.mem s₄.mem := f₄.mono (by simp)
    rw [m₅]; rw [m₃, m₂] at f₄'; exact f₁.trans f₄'

end VG.Proof.X25519.AArch64

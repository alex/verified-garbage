import VerifiedGarbage.Proof.X448.AArch64.Mul

/-!
# X448 on AArch64: pointwise field operations

A pointwise operation fills `TMP` before the carry passes write the output,
permitting input/output aliasing.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem columns_ok {s : State} {base : Addr} (hs : Scr s base) {code : Nat → List Instr}
    {f : Nat → Nat} {rs : List Reg} (hr : .x3 ∉ rs ∧ .x12 ∉ rs) (hb : ∀ i < 16, f i < 2 ^ 62)
    (step : ∀ i < 16, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem → Keeps rs s t →
      WP isa (.block (code i)) t fun u =>
        u.mem = t.mem.writeW (off base (TMP + 8 * i)) (BitVec.ofNat 64 (f i)) ∧ Keeps rs t u) :
    WP isa (.block ((List.range 16).flatMap code)) s fun t =>
      (∀ i < 16, limbs t.mem base TMP i = f i) ∧ Outside base TMP 128 s.mem t.mem ∧ Keeps rs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = f i) ∧ Outside base TMP 128 s.mem t.mem ∧ Keeps rs s t
  have st : ∀ n t, n < 16 → inv n t → WP isa (.block (code n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (step n hn t (hs.of_keeps tk hr) tm tk) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (TMP + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (TMP + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 16) inv st 16 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Reading an input during a pointwise operation. -/
theorem input_limb {s t : State} {base : Addr} {a i : Nat} (h : Outside base TMP 128 s.mem t.mem)
    (ha : Slot a) (hi : i < 16) : limbs t.mem base a i = limbs s.mem base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) hi

/-- Carry propagation after a pointwise operation, with the common frame. -/
theorem columns_normalize {s : State} {base : Addr} (hs : Scr s base) {code : List Instr}
    {o : Nat} (ho : Slot o) (ho8 : o % 8 = 0) {f : Nat → Nat} (hb : ∀ i < 16, f i < 2 ^ 62)
    (hcode : WP isa (.block code) s fun t =>
      (∀ i < 16, limbs t.mem base TMP i = f i) ∧ Outside base TMP 128 s.mem t.mem ∧ Keeps clob s t) :
    WP isa (.block (code ++ normalize o)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ fe t.mem base o % Spec.X448.P = valN f 16 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono hcode fun t ⟨tf, tm, tk⟩ => ?_
  refine WP.mono (normalize_ok (hs.of_keeps tk (by decide)) ho ho8 tf hb) fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨⟨tk.trans (uk.mono ?_), (FieldMem.work tm (by decide) (by decide)).trans um⟩, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro i hi; rw [uf i hi]; exact digit_lt _ _
  · rw [show fe u.mem base o = valN (normalized f) 16 from valN_congr uf, normalized_mod hb]

end VG.Proof.X448.AArch64

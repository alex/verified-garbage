import VerifiedGarbage.Proof.X448.AArch64.Normalize
import VerifiedGarbage.Proof.X448.Product

/-!
# X448 on AArch64: reducing product coefficients

Untrusted: everything here is checked by Lean. Coefficients 16–31 fold
into the lower sixteen according to the relation 2⁴⁴⁸ = 2²²⁴ + 1 modulo p.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem reduceCol_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 16)
    {f : Nat → Nat} (hf : ∀ i < 32, limbs s.mem base ACC i = f i)
    (hb : ∀ i < 32, f i < 2 ^ 60) :
    WP isa (.block (reduceCol k)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 8 * k)) (BitVec.ofNat 64 (reduced f k)) ∧ Keeps [.x4, .x5] s t := by
  have l : ∀ i < 32, InRegions (s.rd ++ s.wr) (off base (ACC + 8 * i)) 8 :=
    fun i hi => hs.read (by simp only [ACC]; omega)
  have enc : ∀ i < 32, (ACC + 8 * i) % 8 = 0 ∧ ACC + 8 * i < 32768 := by
    intro i hi; simp only [ACC]; omega
  have outEnc : (TMP + 8 * k) % 8 = 0 ∧ TMP + 8 * k < 32768 := by
    simp only [TMP]; omega
  have w := hs.write (d := TMP + 8 * k) (n := 8) (by simp only [TMP]; omega)
  have f0 := hf k (by omega)
  have f1 := hf (k + 16) (by omega)
  have f2 := hf (k + 8) (by omega)
  have b0 := hb k (by omega)
  have b1 := hb (k + 16) (by omega)
  have b2 := hb (k + 8) (by omega)
  by_cases h : k < 8
  · have f3 := hf (k + 24) (by omega)
    have b3 := hb (k + 24) (by omega)
    apply WP.of_runBlock
    simp only [reduceCol, h, ite_true, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, ld, st, Size.bytes, addr, State.load, State.store,
      State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write,
      RegUpd.rd_write, RegUpd.wr_write, hs.x3, and_self, read8_eq, write8_eq,
      enc k (by omega), enc (k + 16) (by omega), outEnc,
      l k (by omega), l (k + 16) (by omega), l (k + 24) (by omega), enc (k + 24) (by omega), w,
      Option.map_some, Option.bind_some, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
    · apply congrArg (s.mem.writeW (off base (TMP + 8 * k)))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_true]
      change ((limbs s.mem base ACC k + limbs s.mem base ACC (k + 16)) % 2 ^ 64 +
        limbs s.mem base ACC (k + 24)) % 2 ^ 64 = (f k + f (k + 16) + f (k + 24)) % 2 ^ 64
      rw [f0, f1, f3, Nat.mod_eq_of_lt (show f k + f (k + 16) < 2 ^ 64 by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  · apply WP.of_runBlock
    simp only [reduceCol, h, ite_false, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, ld, st, Size.bytes, addr, State.load, State.store,
      State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write,
      RegUpd.rd_write, RegUpd.wr_write, hs.x3, and_self, read8_eq, write8_eq,
      enc k (by omega), enc (k + 16) (by omega), outEnc,
      l k (by omega), l (k + 16) (by omega), l (k + 8) (by omega), enc (k + 8) (by omega), w,
      Option.map_some, Option.bind_some, reduceCtorEq, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
    · apply congrArg (s.mem.writeW (off base (TMP + 8 * k)))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_false]
      change (((limbs s.mem base ACC k + limbs s.mem base ACC (k + 16)) % 2 ^ 64 +
        limbs s.mem base ACC (k + 8)) % 2 ^ 64 + limbs s.mem base ACC (k + 16)) % 2 ^ 64 =
        (f k + f (k + 16) + (f (k + 8) + f (k + 16))) % 2 ^ 64
      rw [f0, f1, f2, Nat.mod_eq_of_lt (show f k + f (k + 16) < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show f k + f (k + 16) + f (k + 8) < 2 ^ 64 by omega), Nat.add_assoc]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Fold all thirty-two coefficients into sixteen, ready for carries. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 32, limbs s.mem base ACC i = f i) (hb : ∀ i < 32, f i < 2 ^ 60) :
    WP isa (.block ((List.range 16).flatMap reduceCol)) s fun t =>
      (∀ i < 16, limbs t.mem base TMP i = reduced f i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = reduced f i) ∧
    Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4, .x5] s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ft : ∀ i < 32, limbs t.mem base ACC i = f i := by
      intro i hi
      change (word t.mem base (ACC + 8 * i)).toNat = _
      rw [tm.word (Or.inl (by simp only [ACC, TMP]; omega)) (by simp only [ACC]; omega)]
      exact hf i hi
    refine WP.mono (reduceCol_ok (hs.of_keeps tk (by decide)) hn ft hb) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (TMP + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (TMP + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (reduced_bound hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

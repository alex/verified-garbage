import VerifiedGarbage.Proof.Curve448.AArch64.Memory
import VerifiedGarbage.Proof.Framework.Range
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Proof.X448.AArch64

theorem coeff_low {m : Mem} {base : Addr} {i v : Nat}
    (h : coeff m base TMP i = v) (hv : v < 2 ^ 64) :
    (word m base (TMP + 16 * i)).toNat = v := by
  have low := (word m base (TMP + 16 * i)).isLt
  simp only [coeff, pair] at h
  omega

theorem collectStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld .x4 (TMP + 16 * i), st .x4 (o + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (word s.mem base (TMP + 16 * i)) ∧
      Keeps [.x4] s t := by
  have l := hs.read (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega)
  have w := hs.write (d := o + 8 * i) (n := 8) (by simp only [ACC] at ho; omega)
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := by simp only [ACC] at ho; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, ae, oe, and_self, hs.x3, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (fun h => hr (by subst r; decide))

theorem collect_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : Within weakBound f) :
    WP isa (.block (Impl.Curve448.AArch64.collect o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = f i) ∧
      Outside base o 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = f i) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps [.x4] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld .x4 (TMP + 16 * n), st .x4 (o + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (collectStep_ok (hs.of_keeps tk (by decide)) ho ho8 hn) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [ACC] at ho; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [ACC] at ho; omega)
      (by simp only [ACC] at ho; omega)]
    by_cases h : i = n
    · subst i
      rw [ite_eq_left rfl, tm.word (Or.inr (by simp only [ACC, TMP] at ho ⊢; omega))
        (by simp only [TMP]; omega)]
      exact coeff_low (hf n hn) (Nat.lt_trans (hb n hn) (by decide))
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
end VG.Proof.Curve448.AArch64

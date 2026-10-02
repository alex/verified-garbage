import VerifiedGarbage.Proof.Curve448.AArch64.Memory

/-!
# X448 on AArch64: copying field elements

Untrusted: everything here is checked by Lean. Eight persistent limbs are copied. Source and destination are
equal or disjoint; every limb is copied without changing its representation.
-/

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem copyStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld .x4 (a + 8 * i), st .x4 (o + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (word s.mem base (a + 8 * i)) ∧ Keeps clob s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by omega)
  have w := hs.write (d := o + 8 * i) (n := 8) (by omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := ⟨by omega, by omega⟩
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, ae, oe, and_self, hs.x3, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (fun h => hr (by subst r; decide))

theorem copy_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : o = a ∨ o + 128 ≤ a ∨ a + 128 ≤ o) :
    WP isa (.block (copy o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = limbs s.mem base a i) ∧
      Outside base o 128 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 8 → limbs t.mem base a i = limbs s.mem base a i) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld .x4 (a + 8 * n), st .x4 (o + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (copyStep_ok (hs.of_keeps tk (by decide)) ho ha ho8 ha8 hn) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    · intro i hi
      change (word u.mem base (o + 8 * i)).toNat = _
      rw [um, word_write t.mem base (by omega) (by omega)]
      by_cases h : i = n
      · rw [ite_eq_left h, h]; exact ta n (by omega) hn
      · rw [ite_eq_right h]; exact tf i (by omega)
    · intro i hi hi'
      change (word u.mem base (a + 8 * i)).toNat = _
      rw [out.word (by rcases hsep with h | h | h <;> omega) (by omega)]
      exact ta i (by omega) hi'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv st 8 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.Curve448.AArch64

import VerifiedGarbage.Proof.X448.X86.Field

/-!
# X448 on x86 (32-bit): copying field elements

Untrusted: everything here is checked by Lean. Equal or disjoint source
and destination slots preserve the original limbs.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem copyStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096) (hi : i < 28) :
    WP isa (.block [ld .eax (a + 4 * i), st .eax (o + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 4 * i)) (word s.mem base (a + 4 * i)) ∧ Keeps clob s t := by
  refine load_ok hs (by omega) fun t ht => ?_
  refine store_ok (hs.of_upd ht (by decide)) (by omega) fun u hu => WP.block_nil ⟨?_, ?_⟩
  · rw [hu.mem, ht.mem, ht.gpr]
  · exact (ht.rest (by decide)).trans (hu.rest _)

theorem copy_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096)
    (hsep : o = a ∨ o + 112 ≤ a ∨ a + 112 ≤ o) :
    WP isa (.block (copy o a)) s fun t =>
      (∀ i < 28, limbs t.mem base o i = limbs s.mem base a i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 28 → limbs t.mem base a i = limbs s.mem base a i) ∧
    Outside base o 112 s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 28 → inv n t →
      WP isa (.block [ld .eax (a + 4 * n), st .eax (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (copyStep_ok (hs.of_keeps tk (by decide)) ho ha hn) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    · intro i hi
      change (word u.mem base (o + 4 * i)).toNat = _
      rw [um, word_write t.mem base (by omega) (by omega)]
      by_cases h : i = n
      · rw [ite_eq_left h, h]; exact ta n (by omega) hn
      · rw [ite_eq_right h]; exact tf i (by omega)
    · intro i hi hi'
      change (word u.mem base (a + 4 * i)).toNat = _
      rw [out.word (by rcases hsep with h | h | h <;> omega) (by omega)]
      exact ta i (by omega) hi'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

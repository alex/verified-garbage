import VerifiedGarbage.Proof.X448.X86_64.Mul

/-!
# X448 on x86-64: copying field elements

Source and destination are equal or disjoint; every limb is copied without
changing its representation.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem copyStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (hi : i < 16) :
    WP isa (.block [.mov .rax (.mem (sc (a + 8 * i))), .store (sc (o + 8 * i)) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (word s.mem base (a + 8 * i)) ∧ Keeps clob s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by omega)
  have w := hs.write (d := o + 8 * i) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, ea_sc, State.load64,
    State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.wr_setReg,
    hs.rdi, l, w, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (fun h => hr (by subst r; decide))

theorem copy_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192)
    (hsep : o = a ∨ o + 128 ≤ a ∨ a + 128 ≤ o) :
    WP isa (.block (copy o a)) s fun t =>
      (∀ i < 16, limbs t.mem base o i = limbs s.mem base a i) ∧
      Outside base o 128 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 16 → limbs t.mem base a i = limbs s.mem base a i) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 16 → inv n t →
      WP isa (.block [.mov .rax (.mem (sc (a + 8 * n))), .store (sc (o + 8 * n)) .rax]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (copyStep_ok (hs.of_keeps tk (by decide)) ho ha hn) fun u ⟨um, uk⟩ => ?_
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
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv st 16 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86_64

import VerifiedGarbage.Proof.X448.X86_64.Row

/-!
# X448 on x86-64: multiplication loop

Untrusted: everything here is checked by Lean. The invariant relates the
32 coefficients to the rows already accumulated, retaining the two input
field elements throughout the loop.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem mulLoop_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : a + 128 ≤ ACC) (hb : b + 128 ≤ ACC)
    {f g : Nat → Nat} (hf : ∀ k < 16, limbs s.mem base a k = f k)
    (hg : ∀ k < 16, limbs s.mem base b k = g k)
    (fb : ∀ k < 16, f k < radix) (gb : ∀ k < 16, g k < radix)
    (hz : ∀ k < 32, limbs s.mem base ACC k = 0)
    (hc : s.gpr .r10 = 0) (hr : s.gpr .r11 = base) :
    WP isa (.loop (.block (row a b)) .ne) s fun t =>
      (∀ k < 32, limbs t.mem base ACC k = rows f g 16 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps [.rax, .rcx, .rdx, .r10, .r11] s t := by
  let inv := fun n (t : State) => 1 ≤ n ∧ n ≤ 16 ∧
    (∀ k < 32, limbs t.mem base ACC k = rows f g (16 - n) k) ∧
    t.gpr .r10 = BitVec.ofNat 64 (16 - n) ∧ t.gpr .r11 = off base (8 * (16 - n)) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps [.rax, .rcx, .rdx, .r10, .r11] s t
  refine WP.loop (M := isa) inv ?_ 16 s ?_
  · intro n t ⟨hn, hn', tf, tc, tr, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have ft : ∀ k < 16, limbs t.mem base a k = f k := fun k hk =>
      (tm.limbs (Or.inl ha) (Nat.le_trans ha (by decide)) hk).trans (hf k hk)
    have gt : ∀ k < 16, limbs t.mem base b k = g k := fun k hk =>
      (tm.limbs (Or.inl hb) (Nat.le_trans hb (by decide)) hk).trans (hg k hk)
    have bound : ∀ k < 32, rows f g (16 - n) k < 2 ^ 60 := by
      intro k _
      have h1 := rows_bound fb gb (n := 16 - n) (by omega) k
      have h2 := Nat.mul_le_mul_right ((radix - 1) ^ 2) (show 16 - n ≤ 16 by omega)
      have h3 : 16 * (radix - 1) ^ 2 < 2 ^ 60 := by decide
      omega
    refine WP.mono (row_ok ts ha hb (by omega) tc tr tf gt bound gb
      (by rw [ft (16 - n) (by omega)]; exact fb _ (by omega))) fun u ⟨uf, uc, ur, uz, um, uk⟩ => ?_
    have uf' : ∀ k < 32, limbs u.mem base ACC k = rows f g (16 - n + 1) k := by
      intro k hk
      rw [uf k hk, ft (16 - n) (by omega)]
      rfl
    have mem := tm.trans um
    have keep := tk.trans uk
    simp only [eval, uz, Option.map_some]
    by_cases hn1 : n = 1
    · subst n
      exact Or.inl ⟨rfl, uf', mem, keep⟩
    · refine Or.inr ⟨?_, n - 1, by omega, by omega, by omega, ?_, ?_, ?_, mem, keep⟩
      · rw [decide_eq_false (by omega : ¬16 - n + 1 = 16)]; rfl
      · rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact uf'
      · rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact uc
      · rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact ur
  · refine ⟨by decide, by decide, hz, ?_, ?_, Outside.refl _ _ _ _, Keeps.refl _ _⟩
    · exact hc
    · simpa only [Nat.sub_self, Nat.mul_zero, off, BitVec.add_zero] using hr

end VG.Proof.X448.X86_64

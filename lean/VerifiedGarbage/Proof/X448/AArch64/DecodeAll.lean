import VerifiedGarbage.Proof.X448.AArch64.DecodeStore

/-!
# X448 on AArch64: all input-coordinate bytes

Eight limb pairs fill the two coordinate slots. The input lies outside the
writable working space.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Equal input bytes give equal seven-byte chunks. -/
theorem chunk_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 8)
    (h : ∀ j < 56, m' (off p j) = m (off p j)) : chunk m' p i = chunk m p i := by
  apply congrArg VG.Proof.X25519.leNum
  simp only [Spec.X448.bytesAt]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  rw [Offset.add_add]
  exact h _ (by omega)

theorem decodeAll_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block ((List.range 8).flatMap decodePair)) s fun t =>
      (∀ j < 16, limbs t.mem base X1 j = decoded s.mem p j) ∧
      (∀ j < 16, limbs t.mem base X3 j = decoded s.mem p j) ∧
      Outside2 base X1 128 X3 128 s.mem t.mem ∧ Keeps [.x4, .x5, .x7, .x8] s t := by
  let inv := fun n (t : State) =>
    (∀ j < 2 * n, limbs t.mem base X1 j = decoded s.mem p j) ∧
    (∀ j < 2 * n, limbs t.mem base X3 j = decoded s.mem p j) ∧
    Outside2 base X1 (16 * n) X3 (16 * n) s.mem t.mem ∧ Keeps [.x4, .x5, .x7, .x8] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (decodePair n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp := (tk.1 .x2 (by decide)).trans hp
    have tr : ∀ j < 7, InRegions (t.rd ++ t.wr) (off p (7 * n + j)) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr _ (by omega)
    have byte : ∀ j < 56, t.mem (off p j) = s.mem (off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [X1, slot]; omega)) (Or.inr (by simp only [X3, slot]; omega))
    have chunkEq := chunk_congr hn byte
    refine WP.mono (decodePair_ok (hs.of_keeps tk (by decide)) hn tp tr) fun u ⟨um, uk⟩ => ?_
    rw [chunkEq] at um
    have pair := fun (j : Nat) (hj : j < 16) => pairMem_limbs t.mem base hn hj (chunk_lt s.mem p n)
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h1 : j = 2 * n + 1
      · rw [ite_eq_left h1, h1, decoded_odd]
      · rw [ite_eq_right h1]
        by_cases h0 : j = 2 * n
        · rw [ite_eq_left h0, h0, decoded_even]
        · rw [ite_eq_right h0]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h1 : j = 2 * n + 1
      · rw [ite_eq_left h1, h1, decoded_odd]
      · rw [ite_eq_right h1]
        by_cases h0 : j = 2 * n
        · rw [ite_eq_left h0, h0, decoded_even]
        · rw [ite_eq_right h0]; exact ty j (by omega)
    · rw [um]
      exact (tm.mono (by omega) (by omega)).trans (pairMem_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

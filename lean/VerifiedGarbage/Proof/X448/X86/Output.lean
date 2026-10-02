import VerifiedGarbage.Proof.X448.X86.Pack

/-!
# X448 on x86 (32-bit): the output buffer

Output stores cover exactly 56 bytes and preserve the disjoint working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega : 0 + n ≤ 56) (hfar _ (by omega))))

theorem output_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 28).flatMap packLimb)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (fe s.mem base X2) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, decoded t.mem p i = limbs s.mem base X2 i) ∧ Outside p 0 (2 * n) s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (packLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 28, limbs t.mem base X2 j = limbs s.mem base X2 j := by
      intro j hj
      exact congrArg BitVec.toNat (output_word tm (by omega) (by simp only [X2, slot]; omega) hfar)
    have tb : Bounded t.mem base X2 := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (packLimb_ok (p := p) (hs.of_keeps tk (by decide)) tb hn (by rw [tk.1 _ (by decide)]; exact hp)
      (by rw [tk.1 _ (by decide)]; exact hfit)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega))) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, (tm.mono (by decide) (by omega)).trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans (eq n hn)
    · have byte : ∀ j < 2, u.mem (off p (2 * i + j)) = t.mem (off p (2 * i + j)) := by
        intro j hj
        exact um _ (Or.inl (by rw [ofs_off' p (by omega)]; omega))
      simp only [decoded, byteN]
      have b0 := byte 0 (by decide)
      have b1 := byte 1 (by decide)
      simp only [off, Nat.add_zero] at b0 b1
      rw [b0, b1]
      exact tf i (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨packed_bytes tf, tm, tk⟩

end VG.Proof.X448.X86

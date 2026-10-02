import VerifiedGarbage.Proof.X448.AArch64.Pack

/-!
# X448 on AArch64: the output buffer

Output stores cover exactly 56 bytes. The disjoint working space retains the
source limbs and saved registers until the function restores them.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem packPair_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 8) (hp : s.gpr .x1 = p)
    (hw : ∀ j < 7, InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block (packPair i)) s fun t =>
      chunk t.mem p i = packed s.mem base i ∧ Outside p (7 * i) 7 s.mem t.mem ∧ Keeps clob s t := by
  change WP isa (.block (packHead i ++ (List.range 7).flatMap (packByte i))) s _
  rw [WP.block_append_iff]
  refine WP.mono (packHead_ok hs hb hi) fun t ⟨ta, tm, tk⟩ => ?_
  refine WP.mono (writeSeven_ok hi ((tk.1 _ (by decide)).trans hp)
    (by intro j hj; rw [tk.2.2]; exact hw j hj)) fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨?_, tm ▸ um, (tk.mono ?_).trans (uk.mono ?_)⟩
  · have bytes : Spec.X448.bytesAt u.mem (off p (7 * i)) 7 =
        VG.Proof.X25519.leBytes 7 (packed s.mem base i) := by
      apply List.map_congr_left
      intro j hj
      rw [Offset.add_add, uf j (List.mem_range.mp hj), ta]
    change VG.Proof.X25519.leNum _ = _
    rw [bytes]
    exact leNum_leBytes (packed_bound hb hi)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 8 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega : 0 + n ≤ 56) (hfar _ (by omega))))

theorem output_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 8).flatMap packPair)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (fe s.mem base X2) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, chunk t.mem p i = packed s.mem base i) ∧ Outside p 0 (7 * n) s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 8 → inv n t → WP isa (.block (packPair n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 16, limbs t.mem base X2 j = limbs s.mem base X2 j := by
      intro j hj
      exact congrArg BitVec.toNat (output_word tm (by omega) (by simp only [X2, slot]; omega) hfar)
    have tb : Bounded t.mem base X2 := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (packPair_ok (hs.of_keeps tk (by decide)) tb hn ((tk.1 _ (by decide)).trans hp)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega))) fun u ⟨uv, um, uk⟩ => ?_
    have pv : packed t.mem base n = packed s.mem base n := by
      rw [packed, eq (2 * n) (by omega), eq (2 * n + 1) (by omega)]
    refine ⟨?_, (tm.mono (by decide) (by omega)).trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans pv
    · have bytes : Spec.X448.bytesAt u.mem (off p (7 * i)) 7 = Spec.X448.bytesAt t.mem (off p (7 * i)) 7 := by
        apply List.map_congr_left
        intro j hj
        have hj := List.mem_range.mp hj
        rw [Offset.add_add]
        exact um _ (Or.inl (by rw [ofs_off' p (by omega)]; omega))
      change VG.Proof.X25519.leNum _ = _
      rw [bytes]; exact tf i (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv st 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨packed_bytes hb tf, tm, tk⟩

end VG.Proof.X448.AArch64

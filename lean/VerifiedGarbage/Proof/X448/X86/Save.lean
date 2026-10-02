import VerifiedGarbage.Proof.X448.X86.Frame

/-!
# X448 on x86 (32-bit): saving the callee-saved registers

Four scratch words hold the incoming values of ebx, esi, edi, and ebp until
the final restore.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def saved : List Reg := [.ebx, .esi, .edi, .ebp]

def Saved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, word m base (4 * i) = g (saved[i]!)

theorem Saved.outside {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h16 : 16 ≤ o) : Saved base g m' := by
  intro i hi
  exact (ho.word (Or.inl (by omega)) (by omega)).trans (h i hi)

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : 16 ≤ x) (hy : 16 ≤ y) :
    Saved base g m' := by
  intro i hi
  exact (ho.word (Or.inl (by omega)) (Or.inl (by omega)) (by omega)).trans (h i hi)

theorem Saved.field {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {o : Nat} (hm : FieldMem base o m m') (ho : 16 ≤ o) : Saved base g m' := by
  intro i hi
  exact (hm.word (Or.inl (by omega)) (by simp only [ACC]; omega)).trans (h i hi)

theorem saveWords_ok {s : State} {base : Addr} (hc : (s.gpr .eax).setWidth 64 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .eax).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block ((List.range 4).map (fun i => .store (at_ .eax (4 * i)) (saved[i]!)))) s fun t =>
      Saved base s.gpr t.mem ∧ Outside base 0 16 s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (4 * i) = s.gpr (saved[i]!)) ∧
      Outside base 0 16 s.mem t.mem ∧ Keeps [] s t
  have step : ∀ n t, n < 4 → inv n t →
      WP isa (.block [.store (at_ .eax (4 * n)) (saved[n]!)]) t (inv (n + 1)) := by
    intro n t hn' ⟨tv, tm, tk⟩
    have ea : t.ea (at_ .eax (4 * n)) = off base (4 * n) := by
      change addr (t.gpr .eax) (4 * n) = _
      rw [tk.1 _ (by decide), addr_eq (by omega), hc]
    have wr : InRegions t.wr (off base (4 * n)) 4 := by
      rw [tk.2.2]; exact ⟨_, hw, contains_sc (by omega)⟩
    refine wp_store ea wr fun u hu => WP.block_nil ?_
    refine ⟨?_, tm.trans ?_, tk.trans (hu.rest _)⟩
    · intro i hi
      rw [hu.mem, tk.1 _ (by simp)]
      have h := word_write (o := 0) (i := n) (j := i) t.mem base (by omega) (by omega) (s.gpr (saved[n]!))
      simp only [Nat.zero_add] at h
      rw [h]
      by_cases he : i = n
      · rw [ite_eq_left he, he]
      · rw [ite_eq_right he]; exact tv i (by omega)
    · rw [hu.mem]
      exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := 4) inv step 4 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

theorem save_ok {s : State} (hp : Pre s) :
    WP isa (.block save) s fun t =>
      Scr t ((arg s 3).setWidth 64) ∧ Saved ((arg s 3).setWidth 64) s.gpr t.mem ∧
      Outside ((arg s 3).setWidth 64) 0 16 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (at_ .esp 16)) ::
    ((List.range 4).map (fun i => .store (at_ .eax (4 * i)) (saved[i]!)) ++
      [.mov .edi (.reg .eax)]))) s _
  refine loadArg_ok hp rfl rfl rfl (Outside.refl _ _ _ _) (by decide : 3 < 4) fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveWords_ok (base := (arg s 3).setWidth 64) (by rw [ht.gpr]) (by rw [ht.wr]; exact hp.sc_in)
    (by rw [ht.gpr]; exact hp.sc_fit)) fun u ⟨uv, um, uk⟩ => ?_
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (ht.rest (by decide)).trans
    ((uk.mono (by simp)).trans (hv.rest (by decide)))⟩
  · rw [hv.gpr, uk.1 _ (by decide), ht.gpr]
  · rw [hv.wr, uk.2.2, ht.wr]; exact hp.sc_in
  · rw [hv.gpr, uk.1 _ (by decide), ht.gpr]; exact hp.sc_fit
  · intro i hi
    rw [hv.mem, uv i hi, ht.other]
    have he : ∀ i < 4, saved[i]! ≠ .eax := by decide
    exact he i hi
  · rw [hv.mem]
    rw [ht.mem] at um
    exact um

end VG.Proof.X448.X86

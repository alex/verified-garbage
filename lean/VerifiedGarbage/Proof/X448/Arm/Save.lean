import VerifiedGarbage.Proof.X448.Arm.Fill

/-!
# X448 on ARMv7: saving the callee-saved registers

The first eight working-space words preserve the incoming values until the
final restore.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_str wp_mov wp_movw op2_reg)

def Saved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, word m base (4 * i) = g (saved[i]!)

theorem Saved.outside {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h32 : 32 ≤ o) : Saved base g m' := by
  intro i hi
  exact (ho.word (Or.inl (by omega)) (by omega)).trans (h i hi)

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : 32 ≤ x) (hy : 32 ≤ y) :
    Saved base g m' := by
  intro i hi
  exact (ho.word (Or.inl (by omega)) (Or.inl (by omega)) (by omega)).trans (h i hi)

theorem save_ok {s : State} {base : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block ((List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)))) s fun t =>
      Saved base s.gpr t.mem ∧ Outside base 0 32 s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (4 * i) = s.gpr (saved[i]!)) ∧
      Outside base 0 32 s.mem t.mem ∧ Keeps [] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [.str (saved[n]!) .r3 (4 * n)]) t (inv (n + 1)) := by
    intro n t hn' ⟨tv, tm, tk⟩
    have ea : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * n)) = off base (4 * n) := by
      rw [tk.1 _ (by decide), addr_add (by omega), hc]
    have wr : InRegions t.wr (off base (4 * n)) 4 := by
      rw [tk.2.2]; exact ⟨_, hw, contains_sc (by omega)⟩
    refine wp_str (by omega) ea wr fun u hu => WP.block_nil ?_
    refine ⟨?_, tm.trans ?_, tk.trans (rest_keeps (hu.rest _))⟩
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
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

def setupHead : List Instr :=
  (List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)) ++
    [.mov .r12 (.reg .r0), .mov .r0 (.reg .r3), .movw .r6 65535]

theorem setupHead_ok {s : State} {base : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block setupHead) s fun t =>
      Scr t base ∧ t.gpr .r12 = s.gpr .r0 ∧ Saved base s.gpr t.mem ∧
      Outside base 0 32 s.mem t.mem ∧ Keeps [.r12, .r0, .r6] s t := by
  unfold setupHead
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hc hw hn) fun t ⟨tv, tm, tk⟩ => ?_
  refine wp_mov (op2_reg _ _) fun u hu => ?_
  refine wp_mov (op2_reg _ _) fun v hv => ?_
  refine wp_movw fun w hw' => WP.block_nil ?_
  have kr : Keeps [.r12, .r0, .r6] t w := (rest_keeps (hu.rest (by decide))).trans
    ((rest_keeps (hv.rest (by decide))).trans (rest_keeps (hw'.rest (by decide))))
  refine ⟨⟨?_, hw'.gpr, ?_, ?_⟩, ?_, ?_, ?_, (tk.mono (by simp)).trans kr⟩
  · rw [hw'.other _ (by decide), hv.gpr, hu.other _ (by decide), tk.1 _ (by decide)]; exact hc
  · rw [hw'.wr, hv.wr, hu.wr, tk.2.2]; exact hw
  · rw [hw'.other _ (by decide), hv.gpr, hu.other _ (by decide), tk.1 _ (by decide)]; exact hn
  · rw [hw'.other _ (by decide), hv.other _ (by decide), hu.gpr, tk.1 _ (by decide)]
  · rw [hw'.mem, hv.mem, hu.mem]; exact tv
  · rw [hw'.mem, hv.mem, hu.mem]; exact tm

end VG.Proof.X448.Arm

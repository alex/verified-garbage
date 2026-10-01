import VerifiedGarbage.Proof.X448.AArch64.Swap

/-!
# X448 on AArch64: selecting the canonical representative

Untrusted: everything here is checked by Lean. An XOR mask selects each
limb from the original value or the carried temporary value.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def selectStep (i : Nat) : List Instr :=
  [ld .x4 (X2 + 8 * i), ld .x5 (TMP + 8 * i), .logic .eor .x .x5 .x5 .x4,
    .logic .and .x .x5 .x5 .x7, .logic .eor .x .x4 .x4 .x5, st .x4 (X2 + 8 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 16)
    {sw : Bool} (hc : s.gpr .x7 = mask sw) :
    WP isa (.block (selectStep i)) s fun t =>
      t.mem = s.mem.writeW (off base (X2 + 8 * i))
        (if sw then word s.mem base (TMP + 8 * i) else word s.mem base (X2 + 8 * i)) ∧
      Keeps [.x4, .x5] s t := by
  have lx := hs.read (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega)
  have ly := hs.read (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have wx := hs.write (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega)
  have xe : (X2 + 8 * i) % 8 = 0 ∧ X2 + 8 * i < 32768 := by simp only [X2, slot]; omega
  have ye : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [selectStep, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, xe, ye, and_self,
    hs.x3, hc, lx, ly, wx, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  rw [BitVec.xor_comm (word s.mem base (TMP + 8 * i)), (xor_sel sw _ _).1]
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .x7 = mask sw) :
    WP isa (.block ((List.range 16).flatMap selectStep)) s fun t =>
      (∀ i < 16, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
      Outside base X2 128 s.mem t.mem ∧ Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
    Outside base X2 (8 * n) s.mem t.mem ∧ Keeps [.x4, .x5] s t
  have st : ∀ n t, n < 16 → inv n t → WP isa (.block (selectStep n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (selectStep_ok (hs.of_keeps tk (by decide)) hn ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (X2 + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [X2, slot]; omega)
    refine ⟨?_, (tm.mono (by omega) (by omega)).trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (X2 + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [X2, slot]; omega) (by simp only [X2, slot]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h,
        tm.word (Or.inr (by simp only [X2, slot, TMP]; omega)) (by simp only [TMP]; omega),
        tm.word (Or.inr (by omega)) (by simp only [X2, slot]; omega)]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 16) inv st 16 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

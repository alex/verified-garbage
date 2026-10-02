import VerifiedGarbage.Proof.X448.X86.ByteMem

/-!
# X448 on x86 (32-bit): expanding a scalar byte

Public shifts select each bit and write it to its own byte in the working
space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem bitShift_ok {s : State} {j : Nat} (hj : j < 8) :
    WP isa (.block (([.mov .edx (.reg .eax)] : List Instr) ++
      if j = 0 then [] else [.shift .shr .edx j])) s fun t =>
      t.gpr .edx = s.gpr .eax >>> j ∧ t.mem = s.mem ∧ Keeps [.edx] s t := by
  refine wp_mov rfl fun t ht => ?_
  by_cases hz : j = 0
  · subst j
    exact WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩
  · rw [ite_eq_right hz]
    refine wp_shift (by omega) fun u hu => WP.block_nil ⟨?_, hu.mem.trans ht.mem,
      (ht.rest (by decide)).trans (hu.rest (by decide))⟩
    rw [hu.gpr, ht.gpr]

theorem bitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 56)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJ i j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ Keeps [.edx] s t := by
  rw [bitJ, WP.block_append_iff]
  refine WP.mono (bitShift_ok hj) fun t ⟨tv, tm, tk⟩ => ?_
  refine wp_alu (by simp [plain]) rfl fun u hu _ => ?_
  have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
  have ea := us.ea (d := BITS + 8 * i + j) (by simp only [BITS]; omega)
  have wr := us.write (d := BITS + 8 * i + j) (n := 1) (by simp only [BITS]; omega)
  refine wp_store8 ea wr fun v hv => WP.block_nil ⟨?_, tk.trans ?_⟩
  · rw [hv.mem, hu.mem, tm, Reg8.reg, hu.gpr]
    change s.mem.writeW _ ((t.gpr .edx &&& (1 : BitVec 32)).setWidth 8) = _
    rw [tv, ha, bit_byte b j hj, Nat.add_assoc]
  · exact (hu.rest (by decide)).trans (hv.rest _)

/-- Expanding eight bits preserves each byte already written. -/
theorem byteBits_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 56)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (bitJ i))) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitJ i n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (bitJ_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

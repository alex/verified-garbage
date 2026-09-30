import VerifiedGarbage.Proof.X448.X86_64.Swap

/-!
# X448 on x86-64: selecting the canonical representative

Untrusted: everything here is checked by Lean. An XOR mask selects each
limb from the original value or the carried temporary value.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

def selectStep (i : Nat) : List Instr :=
  [.mov .rax (.mem (sc (X2 + 8 * i))), .mov .rdx (.mem (sc (TMP + 8 * i))),
    .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .r8), .alu .xor .rax (.reg .rdx),
    .store (sc (X2 + 8 * i)) .rax]

theorem selectStep_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 16)
    {sw : Bool} (hc : s.gpr .r8 = mask sw) :
    WP isa (.block (selectStep i)) s fun t =>
      t.mem = s.mem.writeW (off base (X2 + 8 * i))
        (if sw then word s.mem base (TMP + 8 * i) else word s.mem base (X2 + 8 * i)) ∧
      Keeps [.rax, .rdx] s t := by
  have lx := hs.read (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega)
  have ly := hs.read (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have wx := hs.write (d := X2 + 8 * i) (n := 8) (by simp only [X2, slot]; omega)
  apply WP.of_runBlock
  simp only [selectStep, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hs.rdi, hc, lx, ly, wx, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  rw [BitVec.xor_comm (word s.mem base (TMP + 8 * i)), (xor_sel sw _ _).1]
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .r8 = mask sw) :
    WP isa (.block ((List.range 16).flatMap selectStep)) s fun t =>
      (∀ i < 16, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
      Outside base X2 128 s.mem t.mem ∧ Keeps [.rax, .rdx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
    Outside base X2 (8 * n) s.mem t.mem ∧ Keeps [.rax, .rdx] s t
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

end VG.Proof.X448.X86_64

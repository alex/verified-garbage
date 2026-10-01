import VerifiedGarbage.Proof.X448.X86.Swap

/-!
# X448 on x86 (32-bit): selecting the canonical representative

Untrusted: everything here is checked by Lean. An XOR mask selects each
limb from the original value or the carried temporary value.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def selectStep (i : Nat) : List Instr :=
  [ld .eax (X2 + 4 * i), ld .edx (TMP + 4 * i), .alu .xor .edx (.reg .eax),
    .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), st .eax (X2 + 4 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 28)
    {sw : Bool} (hc : s.gpr .ecx = mask sw) :
    WP isa (.block (selectStep i)) s fun t =>
      t.mem = s.mem.writeW (off base (X2 + 4 * i))
        (if sw then word s.mem base (TMP + 4 * i) else word s.mem base (X2 + 4 * i)) ∧
      Keeps [.eax, .edx] s t := by
  unfold selectStep
  refine load_ok hs (by simp only [X2, slot]; omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine load_ok ts (by simp only [TMP]; omega) fun u hu => ?_
  have us := ts.of_upd hu (by decide)
  refine wp_alu (by simp [plain]) rfl fun v hv _ => ?_
  have vs := us.of_upd hv (by decide)
  refine wp_alu (by simp [plain]) rfl fun w hw _ => ?_
  have ws := vs.of_upd hw (by decide)
  refine wp_alu (by simp [plain]) rfl fun x hx _ => ?_
  have xs := ws.of_upd hx (by decide)
  refine store_ok xs (by simp only [X2, slot]; omega) fun y hy => WP.block_nil ⟨?_, ?_⟩
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, ht.mem, hx.gpr]
    change _ = s.mem.writeW _ _
    simp only [aluVal]
    rw [hw.other .eax (by decide), hv.other .eax (by decide), hu.other .eax (by decide), ht.gpr,
      hw.gpr, hv.gpr, aluVal, hu.gpr, ht.mem, hu.other .eax (by decide), ht.gpr,
      hv.other .ecx (by decide), hu.other .ecx (by decide), ht.other .ecx (by decide), hc]
    change s.mem.writeW _ (_ ^^^ ((_ ^^^ _) &&& mask sw)) = _
    rw [BitVec.xor_comm (word s.mem base (TMP + 4 * i)), (xor_sel sw _ _).1]
  · exact ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans ((hw.rest (by decide)).trans ((hx.rest (by decide)).trans (hy.rest _))))))

theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .ecx = mask sw) :
    WP isa (.block ((List.range 28).flatMap selectStep)) s fun t =>
      (∀ i < 28, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
      Outside base X2 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
    Outside base X2 (4 * n) s.mem t.mem ∧ Keeps [.eax, .edx] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (selectStep n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (selectStep_ok (hs.of_keeps tk (by decide)) hn ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (X2 + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [X2, slot]; omega)
    refine ⟨?_, (tm.mono (by omega) (by omega)).trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (X2 + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [X2, slot]; omega) (by simp only [X2, slot]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h,
        tm.word (Or.inr (by simp only [X2, slot, TMP]; omega)) (by simp only [TMP]; omega),
        tm.word (Or.inr (by omega)) (by simp only [X2, slot]; omega)]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

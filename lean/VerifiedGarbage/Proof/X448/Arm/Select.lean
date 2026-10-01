import VerifiedGarbage.Proof.X448.Arm.Swap

/-!
# X448 on ARMv7: selecting the canonical representative

Untrusted: everything here is checked by Lean. An XOR mask selects each
limb from the original value or the carried temporary value.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def selectStep (i : Nat) : List Instr :=
  [ld .r3 (X2 + 4 * i), ld .r2 (TMP + 4 * i), .dp .eor .r2 .r2 (.reg .r3),
    .dp .and .r2 .r2 (.reg .r4), .dp .eor .r3 .r3 (.reg .r2), st .r3 (X2 + 4 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 28)
    {sw : Bool} (hc : s.gpr .r4 = mask sw) :
    WP isa (.block (selectStep i)) s fun t =>
      t.mem = s.mem.writeW (off base (X2 + 4 * i))
        (if sw then word s.mem base (TMP + 4 * i) else word s.mem base (X2 + 4 * i)) ∧
      Keeps [.r3, .r2] s t := by
  unfold selectStep
  refine load_ok hs (by simp only [X2, slot]; omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine load_ok ts (by simp only [TMP]; omega) fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun v hv => ?_
  have vs := us.of_upd hv (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun w hw => ?_
  have ws := vs.of_upd hw (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun x hx => ?_
  have xs := ws.of_upd hx (by decide) (by decide)
  refine store_ok xs (by simp only [X2, slot]; omega) fun y hy => WP.block_nil ⟨?_, ?_⟩
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, ht.mem, hx.gpr]
    change _ = s.mem.writeW _ _
    rw [hw.other .r3 (by decide), hv.other .r3 (by decide), hu.other .r3 (by decide), ht.gpr,
      hw.gpr, hv.gpr, hu.gpr, ht.mem, hu.other .r3 (by decide), ht.gpr,
      hv.other .r4 (by decide), hu.other .r4 (by decide), ht.other .r4 (by decide), hc]
    change s.mem.writeW _ (_ ^^^ ((_ ^^^ _) &&& mask sw)) = _
    rw [BitVec.xor_comm (word s.mem base (TMP + 4 * i)), (xor_sel sw _ _).1]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans ((hw.rest (by decide)).trans ((hx.rest (by decide)).trans (hy.rest _))))))

theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .r4 = mask sw) :
    WP isa (.block ((List.range 28).flatMap selectStep)) s fun t =>
      (∀ i < 28, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
      Outside base X2 112 s.mem t.mem ∧ Keeps [.r3, .r2] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base X2 i = if sw then limbs s.mem base TMP i else limbs s.mem base X2 i) ∧
    Outside base X2 (4 * n) s.mem t.mem ∧ Keeps [.r3, .r2] s t
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

end VG.Proof.X448.Arm

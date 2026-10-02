import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Proof.X448.AArch64

/-- Stage all inputs before writing the output, including aliasing cases. -/
theorem stage_ok {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {f : Nat → Nat}
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i))) s fun t =>
      (∀ i < 8, coeff t.mem base TMP i = f i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, coeff t.mem base TMP i = f i) ∧
    Outside base TMP 128 s.mem t.mem ∧ Keeps clob s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (code n ++ Impl.Curve448.AArch64.storeCoeff n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    rw [WP.block_append_iff]
    refine WP.mono (heval n hn t (hs.of_keeps tk (by decide)) tm) fun u ⟨uv, um, uk⟩ => ?_
    refine WP.mono (storeAt_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
      (o := TMP) (k := n) (by simp only [TMP]; omega) (by decide)) fun v ⟨vm, vk⟩ => ?_
    have out : Outside base (TMP + 16 * n) 16 t.mem v.mem := by
      rw [vm, um]; exact putCoeff_outside _ _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans (uk.trans (vk.mono (by decide)))⟩
    intro i hi
    rw [vm, coeff_put _ base _ _ (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · subst i; rw [ite_eq_left rfl]; exact uv
    · rw [ite_eq_right h, um]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

theorem input_limb {base : Addr} {a : Nat} {m m' : Mem}
    (h : Outside base TMP 128 m m') (ha : Slot a) {i : Nat} (hi : i < 8) :
    limbs m' base a i = limbs m base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) (by omega)

theorem stage_normalize {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : Within (2 ^ 118) f)
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i) ++
      Impl.Curve448.AArch64.normalize o)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ fe t.mem base o % Spec.X448.P = valN f 8 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono (stage_ok hs heval) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (normalize_ok (hs.of_keeps uk (by decide)) ho ho8 uf hb) fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨uk.trans (tk.mono (by decide)), (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi; rw [tf i hi]; exact twice_weak hb i hi
  · rw [show fe t.mem base o = valN (folded (folded f)) 8 from valN_congr tf, twice_mod]

theorem small_carry {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < radix * 6) : carry f n < 7 := by
  induction n with
  | zero => simp only [carry]; decide
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    simp only [carry, radix] at *
    omega

theorem pointFinish_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : Within (radix * 6) f) :
    WP isa (.block (Impl.Curve448.AArch64.pointFinish o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = folded f i) ∧ FieldMem base o s.mem t.mem ∧ Keeps clob s t := by
  have cap : ∀ i < 8, f i < 2 ^ 63 + radix := by
    intro i hi; exact Nat.lt_trans (hb i hi) (by decide)
  have out : Within weakBound (folded f) := by
    intro i _
    have hd := digit_lt f i
    have hc := small_carry hb
    simp only [folded, weakBound]
    split <;> omega
  rw [Impl.Curve448.AArch64.pointFinish, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tailPass_ok hs (o := TMP) (by decide) (by decide) (Or.inl rfl) false
    (fun _ => rfl) hf cap) fun u ⟨uf, uc, um, uk⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at uf
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok (hs.of_keeps uk (by decide)) uf uc
    (Nat.lt_trans (small_carry hb) (by decide))) fun v ⟨vf, vm, vk⟩ => ?_
  refine WP.mono (collect_ok ((hs.of_keeps uk (by decide)).of_keeps vk (by decide)) ho ho8 vf out)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨tf, (FieldMem.work um (by decide) (by decide)).trans
    ((FieldMem.work vm (by decide) (by decide)).trans (.output tm)),
    (uk.mono (by decide)).trans ((vk.mono (by decide)).trans (tk.mono (by decide)))⟩
theorem stage_point {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : Within (radix * 6) f)
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i) ++
      Impl.Curve448.AArch64.pointFinish o)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ fe t.mem base o % Spec.X448.P = valN f 8 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono (stage_ok hs heval) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (pointFinish_ok (hs.of_keeps uk (by decide)) ho ho8 uf hb) fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨uk.trans tk, (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi
    rw [tf i hi]
    have hd := digit_lt f i
    have hc := small_carry hb
    simp only [folded, weakBound]
    split <;> omega
  · rw [show fe t.mem base o = valN (folded f) 8 from valN_congr tf, folded_mod]

end VG.Proof.Curve448.AArch64

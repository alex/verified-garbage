import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Mul

/-!
# Squaring

Untrusted: everything here is checked by Lean. `sqr o a` writes the same
limbs as `mul o a a`, from 30 products.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair rows reduced)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs)

def zadds : List Instr := (List.range 4).map fun i => .add .x (Sqr.Z i) (Sqr.A i) (Sqr.A (i + 4))

def doubles : List Instr :=
  (List.range 3).flatMap (fun k => (List.range 3).flatMap fun h =>
    [.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)])

theorem sqr_split (o a : Nat) :
    sqr o a = loadA a ++ consts ++ zadds ++ doubles ++ columns Sqr.R a Sqr.L Sqr.H Sqr.column ++
      finish o := rfl

def zRegs : List Reg := [.x10, .x11, .x13, .x14]

theorem Z_facts : ∀ i < 4, Sqr.Z i ∈ zRegs ∧ ∀ j < 8, Sqr.A j ≠ Sqr.Z i := by decide
theorem Z_inj : ∀ i < 4, ∀ j < 4, i ≠ j → Sqr.Z i ≠ Sqr.Z j := by decide

theorem zadds_ok (s : State) :
    WP isa (.block zadds) s fun t =>
      (∀ i < 4, t.gpr (Sqr.Z i) = s.gpr (Sqr.A i) + s.gpr (Sqr.A (i + 4))) ∧ t.mem = s.mem ∧
      Keeps zRegs s t := by
  have e : zadds = (List.range 4).flatMap fun i => [.add .x (Sqr.Z i) (Sqr.A i) (Sqr.A (i + 4))] := by
    simp only [zadds]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (Sqr.Z i) = s.gpr (Sqr.A i) + s.gpr (Sqr.A (i + 4))) ∧ t.mem = s.mem ∧
    Keeps zRegs s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 4 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  refine WP.mono (add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
  have aA : ∀ j < 8, t.gpr (Sqr.A j) = s.gpr (Sqr.A j) := fun j hj => tk.1 _ (by
    intro h
    simp only [zRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    revert h; revert j; decide)
  refine ⟨fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [uv, aA i (by omega), aA (i + 4) (by omega)]
    · have hne : Sqr.Z i ∉ [Sqr.Z n] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact Z_inj i (by omega) n hn h
      rw [uk.1 _ hne, tv i (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact (Z_facts n hn).1

theorem limb_ne : ∀ h < 3, ∀ k < 3, Sqr.limb h k ≠ Sqr.R.t ∧ Sqr.limb h k ≠ .x3 := by decide

/-- One doubled limb. -/
theorem double_ok {s : State} {base : Addr} (hs : Scr s base) {h k : Nat} (hh : h < 3) (hk : k < 3) :
    WP isa (.block [.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)]) s
      fun t => (∀ d, d + 8 ≤ 8192 → (d = KD + 24 * h + 8 * k ∨ d + 8 ≤ KD + 24 * h + 8 * k ∨
          KD + 24 * h + 8 * k + 8 ≤ d) →
        word t.mem base d = if d = KD + 24 * h + 8 * k then
          s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k) else word s.mem base d) ∧
        Keeps [Sqr.R.t] s t ∧ Outside base KD 72 s.mem t.mem := by
  have hKD : KD = 3648 := rfl
  rw [show [Instr.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)] =
    [Instr.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k)] ++ [st Sqr.R.t (KD + 24 * h + 8 * k)] from rfl,
    WP.block_append_iff]
  refine WP.mono (add_ok s _ _ _) fun u ⟨uv, um, uk⟩ => ?_
  have us : Scr u base := hs.of_keeps uk (by decide)
  refine WP.mono (stw_ok us _ (d := KD + 24 * h + 8 * k) (by omega) (by omega))
    fun t ⟨tw, tO, tg, tr, twr⟩ => ⟨fun d hd hs' => ?_, ?_, by rw [← um]; exact tO.mono (by omega) (by omega)⟩
  · rw [tw d hd hs', uv, um]
  · refine ⟨fun q hq => ?_, tr.trans uk.2.1, twr.trans uk.2.2⟩
    rw [tg, uk.1 q hq]

theorem doubles_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block doubles) s fun t =>
      (∀ h < 3, ∀ k < 3, word t.mem base (KD + 24 * h + 8 * k) =
        s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k)) ∧
      (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KD ∨ KD + 72 ≤ d) → word t.mem base d = word s.mem base d) ∧
      Keeps [Sqr.R.t] s t ∧ Outside base KD 72 s.mem t.mem := by
  have hKD : KD = 3648 := rfl
  have reg : ∀ (t : State), Keeps [Sqr.R.t] s t → ∀ h < 3, ∀ k < 3,
      t.gpr (Sqr.limb h k) = s.gpr (Sqr.limb h k) := fun t tk h hh k hk =>
    tk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (limb_ne h hh k hk).1)
  let inv := fun n (t : State) =>
    (∀ k < n, ∀ h < 3, word t.mem base (KD + 24 * h + 8 * k) =
      s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k)) ∧
    (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
        (∃ h < 3, ∃ k < 3, n ≤ k ∧ d = KD + 24 * h + 8 * k)) → word t.mem base d = word s.mem base d) ∧
    Keeps [Sqr.R.t] s t ∧ Outside base KD 72 s.mem t.mem
  have outer := wp_range_flatMap (M := isa) (N := 3)
    (f := fun k => (List.range 3).flatMap fun h =>
      [.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)]) inv ?_ 3
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, Keeps.refl _ _,
      Outside.refl _ _ _ _⟩
  · refine WP.mono outer fun t ⟨tv, tm, tk, tO⟩ => ⟨fun h hh k hk => tv k hk h hh,
      fun d hd hd' => tm d hd (by omega), tk, tO⟩
  · intro n t hn ⟨tv, tm, tk, tO⟩
    let ininv := fun m (u : State) =>
      (∀ k < n, ∀ h < 3, word u.mem base (KD + 24 * h + 8 * k) =
        s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k)) ∧
      (∀ h < m, word u.mem base (KD + 24 * h + 8 * n) = s.gpr (Sqr.limb h n) + s.gpr (Sqr.limb h n)) ∧
      (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
          (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
          (∃ h < 3, m ≤ h ∧ d = KD + 24 * h + 8 * n)) → word u.mem base d = word s.mem base d) ∧
      Keeps [Sqr.R.t] s u ∧ Outside base KD 72 s.mem u.mem
    have c0 : ∀ d, (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
        (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
        (∃ h < 3, 0 ≤ h ∧ d = KD + 24 * h + 8 * n)) →
        (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨ (∃ h < 3, ∃ k < 3, n ≤ k ∧ d = KD + 24 * h + 8 * k)) := by
      intro d hd'
      rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩ | ⟨h, hh, _, e⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h, hh, k, hk, by omega, e⟩)
      · exact Or.inr (Or.inr ⟨h, hh, n, hn, Nat.le_refl _, e⟩)
    have c3 : ∀ d, (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
        (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k)) →
        (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
          (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
          (∃ h < 3, 3 ≤ h ∧ d = KD + 24 * h + 8 * n)) := by
      intro d hd'
      rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨h, hh, k, hk, hnk, e⟩))
    refine WP.mono (wp_range_flatMap (M := isa) (N := 3) ininv (fun m u hm ⟨uv, uw, um, uk, uO⟩ => ?_) 3
      (by decide) t ⟨tv, fun _ h => absurd h (Nat.not_lt_zero _), fun d hd hd' => tm d hd (c0 d hd'), tk, tO⟩)
      fun u ⟨uv, uw, um, uk, uO⟩ => ⟨fun k hk h hh => ?_, fun d hd hd' => um d hd (c3 d hd'), uk, uO⟩
    · have us : Scr u base := hs.of_keeps uk (by decide)
      refine WP.mono (double_ok us hm hn) fun w ⟨ww, wk, wO⟩ => ⟨fun k hk h hh => ?_, fun h hh => ?_,
        fun d hd hd' => ?_, uk.trans wk, uO.trans wO⟩
      · rw [ww _ (by omega) (by omega), ite_eq_right (by omega)]; exact uv k hk h hh
      · rw [ww _ (by omega) (by omega)]
        by_cases e : h = m
        · subst e; rw [ite_eq_left rfl, reg u uk h hm n hn]
        · rw [ite_eq_right (by omega)]; exact uw h (by omega)
      · have hne : d ≠ KD + 24 * m + 8 * n ∧ (d + 8 ≤ KD + 24 * m + 8 * n ∨
            KD + 24 * m + 8 * n + 8 ≤ d) := by
          rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩ | ⟨h, hh, hmh, e⟩ <;> omega
        have hd2 : d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
            (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
            (∃ h < 3, m ≤ h ∧ d = KD + 24 * h + 8 * n) := by
          rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩ | ⟨h, hh, hmh, e⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl ⟨h, hh, k, hk, hnk, e⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h, hh, by omega, e⟩))
        rw [ww d hd (Or.inr hne.2), ite_eq_right hne.1]
        exact um d hd hd2
    · by_cases e : k = n
      · subst e; exact uw h hh
      · exact uv k (by omega) h hh

theorem sqr_good : Good Sqr.R [Sqr.L, Sqr.H] := by decide
theorem sqr_colRegs : ColRegs Sqr.R [Sqr.L, Sqr.H] := by decide
theorem sqr_ops : ∀ d < 4, (Sqr.column d).all
    (opOk (writes Sqr.R [Sqr.L, Sqr.H]) [Sqr.L, Sqr.H]) = true := by decide
theorem AZ_colWrites : ∀ h < 3, ∀ i < 4, Sqr.limb h i ∉ colWrites Sqr.R [Sqr.L, Sqr.H] := by decide
theorem AZ_pre : ∀ h < 3, ∀ i < 4, Sqr.limb h i ∉ [Sqr.R.t] := by decide
theorem A_z : ∀ i < 8, Mul.A i ∉ zRegs := by decide

/-- The value of limb `i` of half `h`. -/
def lv (f : Nat → Nat) (h i : Nat) : Nat := match h with
  | 0 => f i
  | 1 => f (i + 4)
  | _ => f i + f (i + 4)

theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 64 ≤ ACC) (ho8 : o % 8 = 0) (ha : a + 64 ≤ ACC) (ha8 : a % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) :
    WP isa (.block (sqr o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base a) i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps clob s t := by
  have hA : ACC = 3584 := rfl
  have hKD : KD = 3648 := rfl
  have hST : STAGE = 3840 := rfl
  let f := limbs s.mem base a
  rw [sqr_split, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (loadA_ok hs (by omega) ha8) fun t1 ⟨a1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok t1) fun t2 ⟨mk2, z2, m2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zadds_ok t2) fun t3 ⟨z3, m3, k3⟩ => ?_
  have s3 : Scr t3 base := (s1.of_keeps k2 (by decide)).of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (doubles_ok s3) fun t4 ⟨d4, o4, k4, O4⟩ => ?_
  have s4 : Scr t4 base := s3.of_keeps k4 (by decide)
  have sumlt : ∀ x y : BitVec 64, x.toNat < 2 ^ 63 → y.toNat < 2 ^ 63 →
      (x + y).toNat = x.toNat + y.toNat := fun x y hx hy => by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have fI : ∀ i < 8, f i < Ib := fa
  have A2 : ∀ i < 8, (t2.gpr (Mul.A i)).toNat = f i := fun i hi => by
    rw [k2.1 _ (A_consts i hi), a1 i hi]
  have L4 : ∀ h < 3, ∀ i < 4, (t4.gpr (Sqr.limb h i)).toNat = lv f h i := by
    intro h hh i hi
    rw [k4.1 _ (AZ_pre h hh i hi)]
    obtain rfl | rfl | rfl : h = 0 ∨ h = 1 ∨ h = 2 := by omega
    · change (t3.gpr (Mul.A i)).toNat = _
      rw [k3.1 _ (A_z i (by omega)), A2 i (by omega)]; rfl
    · change (t3.gpr (Mul.A (i + 4))).toNat = _
      rw [k3.1 _ (A_z (i + 4) (by omega)), A2 (i + 4) (by omega)]; rfl
    · change (t3.gpr (Sqr.Z i)).toNat = _
      rw [z3 i hi]
      change (t2.gpr (Mul.A i) + t2.gpr (Mul.A (i + 4))).toNat = _
      rw [sumlt _ _ (by rw [A2 i (by omega)]; have := fI i (by omega); simp only [Ib] at this; omega)
        (by rw [A2 _ (by omega)]; have := fI (i + 4) (by omega); simp only [Ib] at this; omega)]
      rw [A2 i (by omega), A2 _ (by omega)]; rfl
  have lvb : ∀ h < 3, ∀ i < 4, lv f h i < 2 ^ 62 := by
    intro h hh i hi
    have := fI i (by omega); have := fI (i + 4) (by omega)
    obtain rfl | rfl | rfl : h = 0 ∨ h = 1 ∨ h = 2 := by omega
    all_goals simp only [lv, Ib] at *; omega
  have D4 : ∀ h < 3, ∀ k < 3, (word t4.mem base (KD + 24 * h + 8 * k)).toNat = 2 * lv f h k := by
    intro h hh k hk
    rw [d4 h hh k hk]
    have e : t3.gpr (Sqr.limb h k) = t4.gpr (Sqr.limb h k) := (k4.1 _ (AZ_pre h hh k (by omega))).symm
    rw [e, sumlt _ _ (by rw [L4 h hh k (by omega)]; have := lvb h hh k (by omega); omega)
      (by rw [L4 h hh k (by omega)]; have := lvb h hh k (by omega); omega), L4 h hh k (by omega)]
    omega
  have hfit := fits_of fa fa
  let P := fun (t : State) =>
    (∀ h < 3, ∀ i < 4, t.gpr (Sqr.limb h i) = t4.gpr (Sqr.limb h i)) ∧
    (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ STAGE ∨ STAGE + 64 ≤ d) → word t.mem base d = word t4.mem base d)
  have hP : ∀ t u, P t → Keeps (colWrites Sqr.R [Sqr.L, Sqr.H]) t u →
      Outside base STAGE 64 t.mem u.mem → P u := by
    intro t u ⟨pa, pm⟩ k o
    exact ⟨fun h hh i hi => (k.1 _ (AZ_colWrites h hh i hi)).trans (pa h hh i hi),
      fun d hd hd' => (o.word hd' hd).trans (pm d hd hd')⟩
  have hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      sem (srcVal t base a) e (Sqr.column d) Sqr.L = reduced (rows f f 8) d ∧
      sem (srcVal t base a) e (Sqr.column d) Sqr.H = reduced (rows f f 8) (d + 4) := by
    intro d hd t ⟨pa, pm⟩ e
    have hv : ∀ h < 3, ∀ i j, i ≤ j → j < 4 →
        ((srcVal t base a (Sqr.src h (i, j)).1 : Nat) : Int) * (srcVal t base a (Sqr.src h (i, j)).2 : Nat) =
        (if i = j then 1 else 2) * (lv f h i : Int) * lv f h j := by
      intro h hh i j hij hj
      by_cases e : i = j
      · subst e
        simp only [Sqr.src, ite_true, srcVal, pa h hh i hj, L4 h hh i hj]
        ring
      · simp only [Sqr.src, e, ite_false, srcVal, pa h hh j hj, L4 h hh j hj]
        rw [pm _ (by omega) (Or.inl (by omega)), D4 h hh i (by omega)]
        push_cast; ring
    refine sqrCol_ok f (srcVal t base a) ?_ ?_ ?_ e hd
    · intro i j hij hj; rw [hv 0 (by decide) i j hij hj]; rfl
    · intro i j hij hj; rw [hv 1 (by decide) i j hij hj]; rfl
    · intro i j hij hj; rw [hv 2 (by decide) i j hij hj]; simp only [lv]; push_cast; ring
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok sqr_good sqr_colRegs (by decide) (by decide) (by decide) ha8 (by omega)
    hfit sqr_ops P hP hsem s4 ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
    (by rw [k4.1 _ (by decide), k3.1 _ (by decide)]; exact mk2)
    (by rw [k4.1 _ (by decide), k3.1 _ (by decide)]; exact z2))
    fun t5 ⟨p5, i5, k5⟩ => ?_
  have lb : ∀ j < 8, (if j < 4 then chainLimb (reduced (rows f f 8)) 0 j
      else chainLimb (reduced (rows f f 8)) 4 (j - 4)) < radix := fun j _ => by
    split <;> exact Nat.mod_lt _ (by decide)
  refine WP.mono (finish_ok i5.scr (by omega) ho8 i5.mask (stage_limbs i5) lb (i5.cl (by decide))
    (i5.ch (by decide)) hfit.c₀ hfit.c₄)
    fun t6 ⟨v6, o6, k6⟩ => ⟨fun i hi => by rw [v6 i hi, finVal_out _ i hi], ?_, ?_⟩
  · intro x h1 h2
    simp only [ofs] at h1 h2
    have e4 : t4.mem x = t3.mem x := O4 x (by simp only [ofs]; omega)
    rw [o6 x (by simp only [ofs]; omega), i5.out x (by simp only [ofs]; omega), e4, m3, m2, m1]
  · refine (k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans
      ((k5.mono ?_).trans (k6.mono ?_)))))
    all_goals intro r hr; revert r; decide

end VG.Proof.Curve448.AArch64.Fast

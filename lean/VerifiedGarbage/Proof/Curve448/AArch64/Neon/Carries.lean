import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Folds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The coefficients' carries

Untrusted: everything here is checked by Lean. Two chains carry in radix
2²⁸, `0 → 7` and `8 → 15`; their last carries go to coefficients 8 and 0, by
`2⁴⁴⁸ = 2²²⁴ + 1`. With coefficients small enough, every lane holds its exact
value.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon

/-- The carry into coefficient `b + k` of the chain from `b`. -/
def cin (r : Nat → Nat) (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (r (b + k) + cin r b k) / 2 ^ 28

/-- The value of coefficient `b + k` with its carry. -/
abbrev cval (r : Nat → Nat) (b k : Nat) : Nat := r (b + k) + cin r b k

abbrev C7 (r : Nat → Nat) : Nat := cval r 0 7 / 2 ^ 28
abbrev C15 (r : Nat → Nat) : Nat := cval r 8 7 / 2 ^ 28

/-- The limbs after the carries. -/
def limbs28 (r : Nat → Nat) (k : Nat) : Nat :=
  if k < 8 then cval r 0 k % 2 ^ 28 + (if k = 0 then C15 r else 0)
  else cval r 8 (k - 8) % 2 ^ 28 + (if k = 8 then C7 r + C15 r else 0)

/-- Lane `e` of vector register `r` is exactly `x e`. -/
abbrev LaneIs (t : State) (r : Nat) (x : Nat → Nat) : Prop := ∀ e < 2, (vdword (t.v (V r)) e).toNat = x e

theorem cin_le {r : Nat → Nat} {b : Nat} (hr : ∀ k < 8, r (b + k) < 2 ^ 64 - 2 ^ 40) : ∀ k ≤ 8, cin r b k < 2 ^ 36 := by
  intro k hk
  induction k with
  | zero => simp [cin]
  | succ k ih =>
    simp only [cin]
    have := ih (by omega)
    have := hr k (by omega)
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    omega

/-- One step of a chain: carry out of `v_{b+k}` (through `v_t`) into `v_{b+k+1}`. -/
def chainStep (b k t : Nat) : List Instr :=
  [vo (.shift .ushr .d2 (V t) (V (b + k)) 28), vo (.logic .and (V (b + k)) (V (b + k)) (V 30)),
    vo (.add .d2 (V (b + k + 1)) (V (b + k + 1)) (V t))]

theorem chainStep_ok {s : State} {b k t : Nat} (hk : b + k + 1 < 16) (ht : 28 ≤ t ∧ t < 30)
    (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) {x y : Nat → Nat}
    (hx : LaneIs s (b + k) x) (hy : LaneIs s (b + k + 1) y) (hxy : ∀ e < 2, y e + x e / 2 ^ 28 < 2 ^ 64) :
    WP isa (.block (chainStep b k t)) s fun u =>
      LaneIs u (b + k) (fun e => x e % 2 ^ 28) ∧ LaneIs u (b + k + 1) (fun e => y e + x e / 2 ^ 28) ∧
      u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r : VReg, r ≠ V t → r ≠ V (b + k) → r ≠ V (b + k + 1) → u.v r = s.v r) := by
  have n1 : V t ≠ V (b + k) := V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V t ≠ V (b + k + 1) := V_ne _ (by omega) _ (by omega) (by omega)
  have n3 : V (b + k) ≠ V (b + k + 1) := V_ne _ (by omega) _ (by omega) (by omega)
  have n4 : V 30 ≠ V t := V_ne _ (by omega) _ (by omega) (by omega)
  have n5 : V 30 ≠ V (b + k) := V_ne _ (by omega) _ (by omega) (by omega)
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  simp only [chainStep]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_⟩
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, lane_and _ _ hM he, hx e he]
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, lane_map2 _ _ _ he]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx e he, hy e he]
    exact Nat.mod_eq_of_lt (hxy e he)
  · rw [RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

def wrap : List Instr :=
  [vo (.shift .ushr .d2 (V 28) (V 7) 28), vo (.logic .and (V 7) (V 7) (V 30)),
    vo (.shift .ushr .d2 (V 29) (V 15) 28), vo (.logic .and (V 15) (V 15) (V 30)),
    vo (.add .d2 (V 8) (V 8) (V 28)), vo (.add .d2 (V 8) (V 8) (V 29)), vo (.add .d2 (V 0) (V 0) (V 29))]

theorem carries_eq : carries = (List.range 7).flatMap (fun k => chainStep 0 k 28 ++ chainStep 8 k 29) ++ wrap := rfl

/-- Coefficient `b + k` of a chain after `n` steps. -/
def chainAt (r : Nat → Nat) (b n k : Nat) : Nat :=
  if k < n then cval r b k % 2 ^ 28 else if k = n then cval r b k else r (b + k)

theorem chainAt_zero (r : Nat → Nat) (b k : Nat) : chainAt r b 0 k = r (b + k) := by
  rcases k with _ | k <;> simp [chainAt, cval, cin]

/-- The chains, before the last carries. -/
theorem chainLoop_ok {s : State} (r : Nat → Nat → Nat) (hr : ∀ k < 16, LaneIs s k (fun e => r e k))
    (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block ((List.range 7).flatMap (fun k => chainStep 0 k 28 ++ chainStep 8 k 29))) s fun t =>
      (∀ k < 8, LaneIs t k (fun e => chainAt (r e) 0 7 k)) ∧ (∀ k < 8, LaneIs t (8 + k) (fun e => chainAt (r e) 8 7 k)) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧
      (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v) := by
  have ci : ∀ e < 2, ∀ b ∈ [0, 8], ∀ k ≤ 8, cin (r e) b k < 2 ^ 36 := fun e he b hb' k hk =>
    cin_le (fun k hk => hb e he _ (by simp at hb'; omega)) k hk
  let inv := fun n (t : State) =>
    (∀ k < 8, LaneIs t k (fun e => chainAt (r e) 0 n k)) ∧ (∀ k < 8, LaneIs t (8 + k) (fun e => chainAt (r e) 8 n k)) ∧
    t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧
    (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v)
  have i0 : inv 0 s := ⟨fun k hk e he => by dsimp only; rw [chainAt_zero, Nat.zero_add]; exact hr k (by omega) e he,
    fun k hk e he => by dsimp only; rw [chainAt_zero]; exact hr (8 + k) (by omega) e he,
    rfl, rfl, rfl, rfl, hM, fun _ _ _ _ => rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨t0, t8, tm, tg, tr, tw, tM, tv⟩ => ?_) 7
    (by decide) s i0) fun t ht => ht
  · rw [WP.block_append_iff]
    have cn : ∀ e < 2, ∀ b ∈ [0, 8], chainAt (r e) b n n = cval (r e) b n := fun e _ b _ => by
      simp [chainAt]
    have cn1 : ∀ e < 2, ∀ b ∈ [0, 8], chainAt (r e) b n (n + 1) = r e (b + (n + 1)) := fun e _ b _ => by
      simp [chainAt, show ¬ (n + 1 < n) by omega]
    have bnd : ∀ e < 2, ∀ b ∈ [0, 8], r e (b + (n + 1)) + cval (r e) b n / 2 ^ 28 < 2 ^ 64 := fun e he b hb' => by
      have h1 := ci e he b hb' (n + 1) (by omega)
      have h2 := hb e he (b + (n + 1)) (by simp at hb'; omega)
      simp only [cin] at h1
      simp only [cval]
      omega
    refine WP.mono (chainStep_ok (b := 0) (k := n) (t := 28) (by omega) (by omega) tM
      (fun e he => by rw [Nat.zero_add, t0 n (by omega) e he]; dsimp only; rw [cn e he 0 (by simp)])
      (fun e he => by rw [Nat.zero_add, t0 (n + 1) (by omega) e he]; dsimp only; rw [cn1 e he 0 (by simp)])
      (fun e he => bnd e he 0 (by simp))) fun u ⟨ua, ub, um, ug, ur, uw, uv⟩ => ?_
    simp only [Nat.zero_add] at ua ub uv
    have u8 : ∀ k < 8, u.v (V (8 + k)) = t.v (V (8 + k)) := fun k hk =>
      uv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega))
    have uM : ∀ e < 2, (vdword (u.v (V 30)) e).toNat = 2 ^ 28 - 1 := fun e he => by
      rw [uv _ (by decide) (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))]
      exact tM e he
    refine WP.mono (chainStep_ok (b := 8) (k := n) (t := 29) (by omega) (by omega) uM
      (fun e he => by rw [u8 n (by omega), t8 n (by omega) e he]; dsimp only; rw [cn e he 8 (by simp)])
      (fun e he => by
        rw [show 8 + n + 1 = 8 + (n + 1) by omega, u8 (n + 1) (by omega), t8 (n + 1) (by omega) e he]
        dsimp only; rw [cn1 e he 8 (by simp)])
      (fun e he => bnd e he 8 (by simp))) fun w ⟨wa, wb, wm, wg, wr, ww, wv⟩ => ?_
    have w0 : ∀ k < 8, w.v (V k) = u.v (V k) := fun k hk =>
      wv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega))
    refine ⟨fun k hk e he => ?_, fun k hk e he => ?_, wm.trans (um.trans tm), wg.trans (ug.trans tg),
      wr.trans (ur.trans tr), ww.trans (uw.trans tw), fun e he => ?_, fun v h1 h2 h3 => ?_⟩
    · rw [w0 k hk]
      rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ n + 1 < k by omega) with h | rfl | rfl | h
      · rw [uv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
          (V_ne _ (by omega) _ (by omega) (by omega)), t0 k hk e he]
        simp [chainAt, h, show k < n + 1 by omega]
      · rw [ua e he]; simp [chainAt]
      · rw [ub e he]; simp [chainAt, cval, cin]
      · rw [uv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
          (V_ne _ (by omega) _ (by omega) (by omega)), t0 k hk e he]
        simp [chainAt, show ¬ k < n by omega, show k ≠ n by omega, show ¬ k < n + 1 by omega, show k ≠ n + 1 by omega]
    · rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ n + 1 < k by omega) with h | rfl | rfl | h
      · rw [wv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
          (V_ne _ (by omega) _ (by omega) (by omega)), u8 k hk, t8 k hk e he]
        simp [chainAt, h, show k < n + 1 by omega]
      · rw [wa e he]; simp [chainAt]
      · rw [show 8 + (n + 1) = 8 + n + 1 by omega, wb e he]; simp [chainAt, cval, cin]
      · rw [wv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
          (V_ne _ (by omega) _ (by omega) (by omega)), u8 k hk, t8 k hk e he]
        simp [chainAt, show ¬ k < n by omega, show k ≠ n by omega, show ¬ k < n + 1 by omega, show k ≠ n + 1 by omega]
    · rw [wv _ (by decide) (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))]
      exact uM e he
    · rw [wv _ h3 (h1 _ (by omega)) (h1 _ (by omega)), uv _ h2 (h1 _ (by omega)) (h1 _ (by omega)), tv v h1 h2 h3]

/-- The last carries: `C7` into coefficient 8, `C15` into 0 and 8. -/
theorem wrap_ok {t : State} (r : Nat → Nat → Nat) (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40)
    (t0 : ∀ k < 8, LaneIs t k (fun e => chainAt (r e) 0 7 k)) (t8 : ∀ k < 8, LaneIs t (8 + k) (fun e => chainAt (r e) 8 7 k))
    (tM : ∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block wrap) t fun u =>
      (∀ k < 16, LaneIs u k (fun e => limbs28 (r e) k)) ∧ u.mem = t.mem ∧ u.gpr = t.gpr ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → u.v v = t.v v) := by
  have ci : ∀ e < 2, ∀ b ∈ [0, 8], ∀ k ≤ 8, cin (r e) b k < 2 ^ 36 := fun e he b hb' k hk =>
    cin_le (fun k hk => hb e he _ (by simp at hb'; omega)) k hk
  have c7 : ∀ e < 2, cval (r e) 0 7 / 2 ^ 28 < 2 ^ 36 := fun e he => by
    have := ci e he 0 (by simp) 8 (by omega); simp only [cin] at this; exact this
  have c15 : ∀ e < 2, cval (r e) 8 7 / 2 ^ 28 < 2 ^ 36 := fun e he => by
    have := ci e he 8 (by simp) 8 (by omega); simp only [cin] at this; exact this
  have n0_7 : V 0 ≠ V 7 := V_ne _ (by omega) _ (by omega) (by omega)
  have n0_8 : V 0 ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have n0_15 : V 0 ≠ V 15 := V_ne _ (by omega) _ (by omega) (by omega)
  have n0_28 : V 0 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n0_29 : V 0 ≠ V 29 := V_ne _ (by omega) _ (by omega) (by omega)
  have n0_30 : V 0 ≠ V 30 := V_ne _ (by omega) _ (by omega) (by omega)
  have n7_0 : V 7 ≠ V 0 := V_ne _ (by omega) _ (by omega) (by omega)
  have n7_8 : V 7 ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have n7_15 : V 7 ≠ V 15 := V_ne _ (by omega) _ (by omega) (by omega)
  have n7_28 : V 7 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n7_29 : V 7 ≠ V 29 := V_ne _ (by omega) _ (by omega) (by omega)
  have n7_30 : V 7 ≠ V 30 := V_ne _ (by omega) _ (by omega) (by omega)
  have n8_0 : V 8 ≠ V 0 := V_ne _ (by omega) _ (by omega) (by omega)
  have n8_7 : V 8 ≠ V 7 := V_ne _ (by omega) _ (by omega) (by omega)
  have n8_15 : V 8 ≠ V 15 := V_ne _ (by omega) _ (by omega) (by omega)
  have n8_28 : V 8 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n8_29 : V 8 ≠ V 29 := V_ne _ (by omega) _ (by omega) (by omega)
  have n8_30 : V 8 ≠ V 30 := V_ne _ (by omega) _ (by omega) (by omega)
  have n15_0 : V 15 ≠ V 0 := V_ne _ (by omega) _ (by omega) (by omega)
  have n15_7 : V 15 ≠ V 7 := V_ne _ (by omega) _ (by omega) (by omega)
  have n15_8 : V 15 ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have n15_28 : V 15 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n15_29 : V 15 ≠ V 29 := V_ne _ (by omega) _ (by omega) (by omega)
  have n15_30 : V 15 ≠ V 30 := V_ne _ (by omega) _ (by omega) (by omega)
  have n28_0 : V 28 ≠ V 0 := V_ne _ (by omega) _ (by omega) (by omega)
  have n28_7 : V 28 ≠ V 7 := V_ne _ (by omega) _ (by omega) (by omega)
  have n28_8 : V 28 ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have n28_15 : V 28 ≠ V 15 := V_ne _ (by omega) _ (by omega) (by omega)
  have n28_29 : V 28 ≠ V 29 := V_ne _ (by omega) _ (by omega) (by omega)
  have n28_30 : V 28 ≠ V 30 := V_ne _ (by omega) _ (by omega) (by omega)
  have n29_0 : V 29 ≠ V 0 := V_ne _ (by omega) _ (by omega) (by omega)
  have n29_7 : V 29 ≠ V 7 := V_ne _ (by omega) _ (by omega) (by omega)
  have n29_8 : V 29 ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have n29_15 : V 29 ≠ V 15 := V_ne _ (by omega) _ (by omega) (by omega)
  have n29_28 : V 29 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n29_30 : V 29 ≠ V 30 := V_ne _ (by omega) _ (by omega) (by omega)
  have n30_0 : V 30 ≠ V 0 := V_ne _ (by omega) _ (by omega) (by omega)
  have n30_7 : V 30 ≠ V 7 := V_ne _ (by omega) _ (by omega) (by omega)
  have n30_8 : V 30 ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have n30_15 : V 30 ≠ V 15 := V_ne _ (by omega) _ (by omega) (by omega)
  have n30_28 : V 30 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n30_29 : V 30 ≠ V 29 := V_ne _ (by omega) _ (by omega) (by omega)
  have l7 : ∀ e < 2, (vdword (t.v (V 7)) e).toNat = cval (r e) 0 7 := fun e he => by
    rw [t0 7 (by omega) e he]; simp [chainAt]
  have l15 : ∀ e < 2, (vdword (t.v (V 15)) e).toNat = cval (r e) 8 7 := fun e he => by
    rw [t8 7 (by omega) e he]; simp [chainAt]
  have l0 : ∀ e < 2, (vdword (t.v (V 0)) e).toNat = cval (r e) 0 0 % 2 ^ 28 := fun e he => by
    rw [t0 0 (by omega) e he]; simp [chainAt]
  have l8 : ∀ e < 2, (vdword (t.v (V 8)) e).toNat = cval (r e) 8 0 % 2 ^ 28 := fun e he => by
    rw [t8 0 (by omega) e he]; simp [chainAt]
  simp only [wrap]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ?_⟩
  refine ⟨fun k hk e he => ?_, by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV],
    by simp only [RegUpd.rd_setV], by simp only [RegUpd.wr_setV], fun v h1 h2 h3 => ?_⟩
  · rcases (show k = 0 ∨ k = 7 ∨ k = 8 ∨ k = 15 ∨ (0 < k ∧ k < 7) ∨ (8 < k ∧ k < 15) by omega)
      with rfl | rfl | rfl | rfl | ⟨k1, k2⟩ | ⟨k1, k2⟩
    · vred
      rw [lane_map2 _ _ _ he, BitVec.toNat_add, l0 e he, ushr28 _ _ _ he, l15 e he]
      simp only [limbs28, show (0 : Nat) < 8 by decide, ite_true]
      have := c15 e he
      exact Nat.mod_eq_of_lt (by omega)
    · vred
      rw [lane_and _ _ tM he, l7 e he]
      simp [limbs28]
    · vred
      rw [lane_map2 _ _ _ he, BitVec.toNat_add, lane_map2 _ _ _ he,
        BitVec.toNat_add, l8 e he, ushr28 _ _ _ he, l7 e he, ushr28 _ _ _ he, l15 e he]
      have := c7 e he; have := c15 e he
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [limbs28, show ¬ (8 : Nat) < 8 by decide, ite_false, ite_true, Nat.sub_self, C7, C15]
      omega
    · vred
      rw [lane_and _ _ tM he, l15 e he]
      simp [limbs28]
    · have hv : ∀ n ∈ [0, 7, 8, 15, 28, 29], V k ≠ V n := fun n hn =>
        V_ne _ (by omega) _ (by simp at hn; omega) (by simp at hn; omega)
      rw [RegUpd.v_setV_of_ne _ _ (hv 0 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 15 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 29 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 7 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 28 (by simp)), t0 k (by omega) e he]
      simp [chainAt, limbs28, show k < 7 by omega, show k < 8 by omega, show k ≠ 0 by omega]
    · have hv : ∀ n ∈ [0, 7, 8, 15, 28, 29], V k ≠ V n := fun n hn =>
        V_ne _ (by omega) _ (by simp at hn; omega) (by simp at hn; omega)
      rw [RegUpd.v_setV_of_ne _ _ (hv 0 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 15 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 29 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 7 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 28 (by simp)), show k = 8 + (k - 8) by omega, t8 (k - 8) (by omega) e he]
      simp [chainAt, limbs28, show k - 8 < 7 by omega, show ¬ (8 + (k - 8) < 8) by omega]
      intro h; omega
  · rw [RegUpd.v_setV_of_ne _ _ (h1 0 (by decide)), RegUpd.v_setV_of_ne _ _ (h1 8 (by decide)),
      RegUpd.v_setV_of_ne _ _ (h1 8 (by decide)), RegUpd.v_setV_of_ne _ _ (h1 15 (by decide)),
      RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ (h1 7 (by decide)), RegUpd.v_setV_of_ne _ _ h2]

theorem carries_ok {s : State} (r : Nat → Nat → Nat) (hr : ∀ k < 16, LaneIs s k (fun e => r e k))
    (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block carries) s fun t =>
      (∀ k < 16, LaneIs t k (fun e => limbs28 (r e) k)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v) := by
  rw [carries_eq, WP.block_append_iff]
  exact WP.mono (chainLoop_ok r hr hb hM) fun t ⟨t0, t8, tm, tg, tr, tw, tM, tv⟩ =>
    WP.mono (wrap_ok r hb t0 t8 tM) fun u ⟨ul, um, ug, ur, uw, uv⟩ =>
      ⟨ul, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw, fun v h1 h2 h3 => (uv v h1 h2 h3).trans (tv v h1 h2 h3)⟩

/-! ## The value -/

/-- `Σ_{k<n} f k xᵏ`. -/
def psum (f : Nat → Nat) (x : Int) : Nat → Int
  | 0 => 0
  | n + 1 => psum f x n + f n * x ^ n

/-- A chain keeps the value: its limbs and its last carry are its coefficients. -/
theorem chain_val (r : Nat → Nat) (b : Nat) (n : Nat) :
    psum (fun k => cval r b k % 2 ^ 28) (2 ^ 28) n + cin r b n * (2 ^ 28 : Int) ^ n =
      psum (fun k => r (b + k)) (2 ^ 28) n := by
  induction n with
  | zero => simp [psum, cin]
  | succ n ih =>
    simp only [psum, cin]
    have e' : cval r b n % 2 ^ 28 + (cval r b n / 2 ^ 28) * 2 ^ 28 = r (b + n) + cin r b n := by
      simp only [cval]; omega
    have e : ((cval r b n % 2 ^ 28 : Nat) : Int) + ((cval r b n / 2 ^ 28 : Nat) : Int) * 2 ^ 28 =
        (r (b + n) : Int) + cin r b n := by exact_mod_cast e'
    rw [← ih]
    have : ((cval r b n % 2 ^ 28 : Nat) : Int) * (2 ^ 28) ^ n + ((cval r b n / 2 ^ 28 : Nat) : Int) * (2 ^ 28) ^ (n + 1) =
        ((r (b + n) : Int) + cin r b n) * (2 ^ 28) ^ n := by rw [← e]; ring
    linarith

theorem limbs28_val (r : Nat → Nat) :
    psum (limbs28 r) (2 ^ 28) 16 = psum r (2 ^ 28) 16 - (C15 r : Int) * ((2 ^ 28) ^ 16 - (2 ^ 28) ^ 8 - 1) := by
  have h0 := chain_val r 0 8
  have h8 := chain_val r 8 8
  have c7 : cin r 0 8 = C7 r := rfl
  have c15 : cin r 8 8 = C15 r := rfl
  rw [c7] at h0
  rw [c15] at h8
  simp only [psum, limbs28, Nat.zero_add] at h0 h8 ⊢
  simp only [show (0 : Nat) < 8 by decide, show (1 : Nat) < 8 by decide, show (2 : Nat) < 8 by decide,
    show (3 : Nat) < 8 by decide, show (4 : Nat) < 8 by decide, show (5 : Nat) < 8 by decide,
    show (6 : Nat) < 8 by decide, show (7 : Nat) < 8 by decide, show ¬ (8 : Nat) < 8 by decide,
    show ¬ (9 : Nat) < 8 by decide, show ¬ (10 : Nat) < 8 by decide, show ¬ (11 : Nat) < 8 by decide,
    show ¬ (12 : Nat) < 8 by decide, show ¬ (13 : Nat) < 8 by decide, show ¬ (14 : Nat) < 8 by decide,
    show ¬ (15 : Nat) < 8 by decide, ite_true, ite_false, Nat.reduceSub, Nat.cast_add,
    ] at ⊢
  simp only [show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
    show (4 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 0 by decide,
    show (7 : Nat) ≠ 0 by decide, show (9 : Nat) ≠ 8 by decide, show (10 : Nat) ≠ 8 by decide,
    show (11 : Nat) ≠ 8 by decide, show (12 : Nat) ≠ 8 by decide, show (13 : Nat) ≠ 8 by decide,
    show (14 : Nat) ≠ 8 by decide, show (15 : Nat) ≠ 8 by decide, ite_false, 
    Nat.cast_zero, Int.add_zero] at ⊢
  linear_combination h0 + (2 ^ 28) ^ 8 * h8

end VG.Proof.Curve448.AArch64.Neon

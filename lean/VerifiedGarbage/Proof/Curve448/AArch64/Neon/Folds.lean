import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Arith
import VerifiedGarbage.Proof.Framework.Range

/-!
# Combining the halves' coefficients

Untrusted: everything here is checked by Lean. `foldS` turns the coefficients
`S_q` into `S_d - S_{d+8}` (in `v_d`) and `-S_d` (in `v_{d+8}`); `foldU` adds
`U_{d+8}` (in `v_{16+d}`) to both.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon

/-- Lane `e` of vector register `r` is `f r e`, modulo 2⁶⁴. -/
abbrev LaneEq (t : State) (r : Nat) (x : Nat → Int) : Prop := ∀ e < 2, lane (t.v (V r)) e % M64 = x e % M64

def foldSChunk (d : Nat) : List Instr :=
  [vo (.mov (V 28) (V (d + 8))), vo (.sub .d2 (V (d + 8)) (V 31) (V d)), vo (.sub .d2 (V d) (V d) (V 28))]

theorem foldS_eq : foldS = (List.range 7).flatMap foldSChunk ++ [vo (.sub .d2 (V 15) (V 31) (V 7))] := rfl

theorem cong_sub {x y a b : Int} (hx : x % M64 = a % M64) (hy : y % M64 = b % M64) :
    (x - y) % M64 = (a - b) % M64 := by rw [Int.sub_emod, hx, hy, ← Int.sub_emod]

theorem cong_add {x y a b : Int} (hx : x % M64 = a % M64) (hy : y % M64 = b % M64) :
    (x + y) % M64 = (a + b) % M64 := by rw [Int.add_emod, hx, hy, ← Int.add_emod]

theorem cong_neg {x a : Int} (hx : x % M64 = a % M64) : (0 - x) % M64 = (-a) % M64 := by
  rw [cong_sub (x := 0) (a := 0) rfl hx, Int.zero_sub]

theorem lane_zero (e : Nat) : lane (0 : BitVec 128) e = 0 := by simp [lane, vdword]

theorem foldSChunk_ok {s : State} {d : Nat} (hd : d < 7) {a b : Nat → Int} (ha : LaneEq s d a)
    (hb : LaneEq s (d + 8) b) (h31 : s.v (V 31) = 0) :
    WP isa (.block (foldSChunk d)) s fun t =>
      LaneEq t d (fun e => a e - b e) ∧ LaneEq t (d + 8) (fun e => - a e) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, r ≠ V 28 → r ≠ V d → r ≠ V (d + 8) → t.v r = s.v r) := by
  have n1 : V 28 ≠ V d := V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V 28 ≠ V (d + 8) := V_ne _ (by omega) _ (by omega) (by omega)
  have n3 : V (d + 8) ≠ V d := V_ne _ (by omega) _ (by omega) (by omega)
  have n4 : V 31 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n5 : V 31 ≠ V (d + 8) := V_ne _ (by omega) _ (by omega) (by omega)
  have n6 : V d ≠ V 28 := n1.symm
  have n7 : V d ≠ V (d + 8) := n3.symm
  have n8 : V (d + 8) ≠ V 28 := n2.symm
  have n9 : V 28 ≠ V 31 := n4.symm
  simp only [foldSChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_⟩
  · rw [RegUpd.v_setV_self, lane_sub _ _ he]
    exact cong_sub (ha e he) (hb e he)
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, lane_sub _ _ he, h31, lane_zero]
    exact cong_neg (ha e he)
  · rw [RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h1]

theorem foldS_ok {s : State} (x : Nat → Nat → Int) (hx : ∀ q < 15, LaneEq s q (x q)) (h31 : s.v (V 31) = 0) :
    WP isa (.block foldS) s fun t =>
      (∀ d < 8, LaneEq t d (fun e => x d e - (if d < 7 then x (d + 8) e else 0))) ∧
      (∀ d < 8, LaneEq t (d + 8) (fun e => - x d e)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, (∀ n < 16, r ≠ V n) → r ≠ V 28 → t.v r = s.v r) := by
  rw [foldS_eq, WP.block_append_iff]
  let inv := fun n (t : State) =>
    (∀ d < 7, LaneEq t d (fun e => x d e - (if d < n then x (d + 8) e else 0))) ∧
    (∀ d < 7, LaneEq t (d + 8) (fun e => if d < n then - x d e else x (d + 8) e)) ∧
    LaneEq t 7 (x 7) ∧ t.v (V 31) = 0 ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, (∀ n < 16, r ≠ V n) → r ≠ V 28 → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨ta, tb, t7, t31, tm, tg, tr, tw, tv⟩ => ?_)
    7 (by decide) s ⟨fun d hd e he => by simp [hx d (by omega) e he], fun d hd e he => by simp [hx (d + 8) (by omega) e he],
      hx 7 (by decide), h31, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun t ⟨ta, tb, t7, t31, tm, tg, tr, tw, tv⟩ => ?_
  · refine WP.mono (foldSChunk_ok hn (ta n hn) (tb n hn) t31) fun u ⟨ua, ub, um, ug, ur, uw, uv⟩ =>
      ⟨fun d hd e he => ?_, fun d hd e he => ?_, ?_, ?_, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw,
        fun r h1 h2 => (uv r h2 (h1 n (by omega)) (h1 (n + 8) (by omega))).trans (tv r h1 h2)⟩
    · rcases (show d = n ∨ d ≠ n by omega) with rfl | hne
      · rw [ua e he]; simp
      · rw [uv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) hne)
          (V_ne _ (by omega) _ (by omega) (by omega)), ta d hd e he]
        simp only [show (d < n + 1) = (d < n) from propext (by omega)]
    · rcases (show d = n ∨ d ≠ n by omega) with rfl | hne
      · rw [ub e he]; simp
      · rw [uv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
          (V_ne _ (by omega) _ (by omega) (by omega)), tb d hd e he]
        simp only [show (d < n + 1) = (d < n) from propext (by omega)]
    · intro e he
      rw [uv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega)), t7 e he]
    · rw [uv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega)), t31]
  · refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr
      ⟨fun d hd e he => ?_, fun d hd e he => ?_, tm, tg, tr, tw, fun r h1 h2 => ?_⟩⟩
    · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]
      rcases (show d < 7 ∨ d = 7 by omega) with h | rfl
      · rw [ta d h e he]
      · rw [t7 e he]; simp
    · rcases (show d < 7 ∨ d = 7 by omega) with h | rfl
      · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega)), tb d h e he]; simp [h]
      · rw [RegUpd.v_setV_self, lane_sub _ _ he, t31, lane_zero]
        exact cong_neg (t7 e he)
    · rw [RegUpd.v_setV_of_ne _ _ (h1 15 (by decide)), tv r h1 h2]

/-- After `U`: `U_{d+8}`, in `v_{16+d}`, into `v_d` and `v_{d+8}`. -/
def foldUChunk (d : Nat) : List Instr :=
  [vo (.add .d2 (V d) (V d) (V (16 + d))), vo (.add .d2 (V (d + 8)) (V (d + 8)) (V (16 + d)))]

theorem foldU_eq : foldU = (List.range 7).flatMap foldUChunk := rfl

theorem foldU_ok {s : State} (x y : Nat → Nat → Int) (hx : ∀ k < 16, LaneEq s k (x k))
    (hy : ∀ d < 7, LaneEq s (16 + d) (y d)) :
    WP isa (.block foldU) s fun t =>
      (∀ k < 16, LaneEq t k (fun e => x k e + (if k < 7 then y k e else if 8 ≤ k ∧ k < 15 then y (k - 8) e else 0))) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, (∀ n < 16, r ≠ V n) → t.v r = s.v r) := by
  rw [foldU_eq]
  let inv := fun n (t : State) =>
    (∀ k < 16, LaneEq t k (fun e => x k e + (if k < n then y k e else if 8 ≤ k ∧ k < 8 + n then y (k - 8) e else 0))) ∧
    (∀ d < 7, LaneEq t (16 + d) (y d)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, (∀ n < 16, r ≠ V n) → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨ta, ty, tm, tg, tr, tw, tv⟩ => ?_)
    7 (by decide) s ⟨fun k hk e he => by simp [hx k hk e he, show ¬ (8 ≤ k ∧ k < 8) by omega], hy, rfl, rfl, rfl,
      rfl, fun _ _ => rfl⟩)
    fun t ⟨ta, _, tm, tg, tr, tw, tv⟩ => ⟨fun k hk e he => by rw [ta k hk e he], tm, tg, tr, tw, tv⟩
  simp only [foldUChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr
    ⟨fun k hk e he => ?_, fun d hd e he => ?_, tm, tg, tr, tw, fun r h1 => ?_⟩⟩
  · have hn8 : V (n + 8) ≠ V n := V_ne _ (by omega) _ (by omega) (by omega)
    have hU8 : V (16 + n) ≠ V n := V_ne _ (by omega) _ (by omega) (by omega)
    rcases (show k = n + 8 ∨ k = n ∨ (k ≠ n ∧ k ≠ n + 8) by omega) with rfl | rfl | ⟨k1, k2⟩
    · rw [RegUpd.v_setV_self, lane_add _ _ he, RegUpd.v_setV_of_ne _ _ hn8,
        RegUpd.v_setV_of_ne _ _ hU8]
      rw [cong_add (ta _ hk e he) (ty n hn e he)]
      congr 1
      by_cases h : n + 8 < n <;> simp [h] <;> split <;> omega
    · rw [RegUpd.v_setV_of_ne _ _ hn8.symm, RegUpd.v_setV_self, lane_add _ _ he,
        cong_add (ta _ hk e he) (ty k hn e he)]
      congr 1
      simp only [show k < k + 1 from by omega, ite_true, show ¬ k < k from by omega, ite_false]
      split <;> omega
    · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) k2),
        RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) k1), ta k hk e he]
      congr 2
      by_cases h1 : k < n <;> by_cases h2 : k < n + 1 <;> by_cases h3 : 8 ≤ k ∧ k < 8 + n <;>
        by_cases h4 : 8 ≤ k ∧ k < 8 + (n + 1) <;> simp [h1, h2, h3, h4] <;> omega
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega)),
      RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega)), ty d hd e he]
  · rw [RegUpd.v_setV_of_ne _ _ (h1 _ (by omega)), RegUpd.v_setV_of_ne _ _ (h1 _ (by omega)), tv r h1]

end VG.Proof.Curve448.AArch64.Neon

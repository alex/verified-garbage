import VerifiedGarbage.Proof.Ed25519.Arm.Field

/-!
# Ed25519 on ARMv7: the conditional swap

`cswap x y` swaps the elements at `x` and `y` if the mask in `r9` is `-1` and
leaves them if it is `0` (`cswap_ok`).
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm
open VG.Proof.X25519.Arm

theorem sel0 (a c : BitVec 32) : a ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel0' (a c : BitVec 32) : c ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 0)) = c := by simp

theorem sel1 (a c : BitVec 32) : a ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem sel1' (a c : BitVec 32) : c ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 1)) = a := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

section
variable {b : BitVec 32}

/-- While swapping `x` and `y` from `s0`, after `n` limbs. -/
structure SwapInv (b : BitVec 32) (x y sw : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3, .r4] s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 x, 4 * n⟩, ⟨State.addr b + BitVec.ofNat 64 y, 4 * n⟩]
    s0.mem s.mem
  lx : ∀ j < n, limb s.mem (State.addr b) x j =
    sel sw (limb s0.mem (State.addr b) x j) (limb s0.mem (State.addr b) y j)
  ly : ∀ j < n, limb s.mem (State.addr b) y j =
    sel sw (limb s0.mem (State.addr b) y j) (limb s0.mem (State.addr b) x j)

theorem cswap_ok {x y : Nat} (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096) (hxy : x + 64 ≤ y ∨ y + 64 ≤ x)
    {s0 : State} (hc : Ctx b s0) {sw : Nat} (hsw : sw ≤ 1) (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block (cswap x y)) s0 (SwapInv b x y sw s0 16) := by
  refine wp_range_flatMap (M := isa) (SwapInv b x y sw s0) (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  have wx : wd s.mem (State.addr b) (x + 4 * k) = limb s0.mem (State.addr b) x k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have wy : wd s.mem (State.addr b) (y + 4 * k) = limb s0.mem (State.addr b) y k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  unfold Impl.X25519.Arm.cswapStep
  refine ldr0_ok hcs (d := x + 4 * k) (by omega) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r2]) (by decide)) (by decide)) (d := y + 4 * k) (by omega)
    fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 v5 => wp_dp (op2_reg _ _) fun t6 v6 => ?_
  have hr6 : Rest [.r2, .r3, .r4] s t6 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))))
  have hc6 : Ctx b t6 := hcs.of_rest hr6 (by decide)
  refine str0_ok hc6 (d := x + 4 * k) (by omega) fun t7 v7 => ?_
  refine str0_ok (hc6.of_rest (v7.rest []) (by decide)) (d := y + 4 * k) (by omega) fun t8 v8 => ?_
  refine WP.block_nil ?_
  -- The values.
  have eX : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (x + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  have eY : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (y + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
  have e6x : t6.gpr .r2 = t2.gpr .r2 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& (0 - BitVec.ofNat 32 sw)) := by
    rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.other _ (by decide), v4.gpr]
    show _ ^^^ (t3.gpr .r4 &&& t3.gpr .r9) = _
    rw [v3.gpr, em]; rfl
  have e6y : t6.gpr .r3 = t2.gpr .r3 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& (0 - BitVec.ofNat 32 sw)) := by
    rw [v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v5.other _ (by decide),
      v4.gpr]
    show _ ^^^ (t3.gpr .r4 &&& t3.gpr .r9) = _
    rw [v3.gpr, em]; rfl
  have hm8 : t8.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (x + 4 * k)) (t6.gpr .r2)).writeW
      (State.addr b + BitVec.ofNat 64 (y + 4 * k)) (t6.gpr .r3) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have vx : (t6.gpr .r2).toNat = sel sw (limb s0.mem (State.addr b) x k) (limb s0.mem (State.addr b) y k) := by
    rw [e6x, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0]; rfl
    · rw [sel1]; rfl
  have vy : (t6.gpr .r3).toNat = sel sw (limb s0.mem (State.addr b) y k) (limb s0.mem (State.addr b) x k) := by
    rw [e6y, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0']; rfl
    · rw [sel1']; rfl
  refine ⟨h.rest.trans (hr6.trans ((v7.rest _).trans (v8.rest _))), ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · rw [limb, hm8, wd_write_other _ _ _ (by omega) (by omega) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.lx j hj
    · rw [wd_write_self, vx]
  · rw [limb, hm8]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.ly j hj
    · rw [wd_write_self, vy]

end

end VG.Proof.Ed25519.Arm

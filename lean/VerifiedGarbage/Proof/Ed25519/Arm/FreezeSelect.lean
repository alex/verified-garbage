import VerifiedGarbage.Proof.Ed25519.Arm.FreezeSteps

/-! Select the reduced limbs without a data-dependent branch. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem freezeSelect_ok {b : BitVec 32} {s0 : State} (hc : Ctx b s0) {sw : Nat}
    (hsw : sw ≤ 1) (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block freezeSelect) s0 fun t => Rest [.r2, .r3] s0 t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s0.mem t.mem ∧
      ∀ k < 16, limb t.mem (State.addr b) FR k =
        sel sw (limb s0.mem (State.addr b) FR k) (limb s0.mem (State.addr b) FY k) := by
  have hR : FR = 1472 := rfl
  have hY : FY = 1536 := rfl
  refine WP.mono (fill_regs_ok (ws := [.r2, .r3]) (by decide) (src := selectSrc)
    (f := fun k => sel sw (limb s0.mem (State.addr b) FR k) (limb s0.mem (State.addr b) FY k))
    hc (by decide) (fun k hk s h => ?_)) fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  have hcs := hc.of_rest h.rest (by decide)
  unfold selectSrc
  refine ldr0_ok hcs (d := FR + 4 * k) (by omega) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide))
    (d := FY + 4 * k) (by omega) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 =>
    wp_dp (op2_reg _ _) fun t5 v5 => WP.block_nil ?_
  have ex : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (FR + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  have ey : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (FY + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide),
      h.rest.gpr _ (by decide), h9]
  have hx : limb s.mem (State.addr b) FR k = limb s0.mem (State.addr b) FR k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have hy : limb s.mem (State.addr b) FY k = limb s0.mem (State.addr b) FY k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨?_, (v1.rest (by decide)).trans ((v2.rest (by decide)).trans
    ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans (v5.rest (by decide))))),
    by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩
  rw [v5.gpr]
  show (t4.gpr .r3 ^^^ t4.gpr .r2).toNat = _
  rw [v4.other .r3 (by decide), v4.gpr]
  show (t3.gpr .r3 ^^^ (t3.gpr .r2 &&& t3.gpr .r9)).toNat = _
  rw [v3.other .r3 (by decide), v3.gpr, em]
  show (t2.gpr .r3 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& _)).toNat = _
  rw [ex, ey]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · rw [sel0r]; exact hx
  · rw [sel1r]; exact hy

end VG.Proof.Ed25519.Arm

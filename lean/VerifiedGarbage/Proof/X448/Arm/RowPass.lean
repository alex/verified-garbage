import VerifiedGarbage.Proof.X448.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.Pass

/-!
# X448 on ARMv7: multiplication-row carry propagation

Untrusted: everything here is checked by Lean. The instruction rules and
carry-chain arithmetic are shared with X25519. This pass handles the
28 limbs of X448.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

/-- After `k` limbs of `carryPass rb o src` from `s0`, for the sums `c` and the
carry `cin`. -/
structure CarryInv (rb : Reg) (o : Nat) (s0 : State) (c : Nat → Nat) (cin k : Nat) (s : State) :
    Prop where
  rest : Rest [.r2, .r3, .r4, .r5] s0 s
  r5 : (s.gpr .r5).toNat = chain c cin k
  frame : Frame [⟨State.addr (s0.gpr rb) + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem (State.addr (s0.gpr rb)) (o + 4 * j) = out c cin j

theorem carryPass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.r2, .r3, .r4, .r5]) (ho : o + 112 ≤ 4096)
    (hfit : (s0.gpr rb).toNat + o + 112 ≤ 2 ^ 32)
    (hw : ∀ k < 28, InRegions s0.wr (State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k)) 4)
    (h6 : s0.gpr .r6 = mask16) (h5 : (s0.gpr .r5).toNat = cin)
    (hc : ∀ k < 28, c k + 65536 ≤ 2 ^ 32) (hcin : cin < 65536)
    (hsrc : ∀ k < 28, ∀ s, CarryInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (carryPass rb o src)) s0 (CarryInv rb o s0 c cin 28) := by
  have hr := not_mem4 hrb
  refine wp_range_flatMap (M := isa) (CarryInv rb o s0 c cin) (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h5]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h3, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1, hr.2.2.1]), h.rest.gpr _ hrb]
  have h51 : s1.gpr .r5 = s.gpr .r5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (VG.Proof.X25519.Arm.carryStep_ok (a := State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k))
    ⟨hr.2.1, hr.2.2.1⟩ (by omega) (by rw [hrb1]; exact ea (by omega))
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [hr1.gpr _ (by decide), h.rest.gpr _ (by decide), h6])
    (by rw [h3, h51, h.r5]; exact hsum)) fun s2 ⟨e5, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h3, h51, h.r5] at e5 hv
  rw [hm1] at hm2
  refine ⟨h.rest.trans ((hr1.mono (by decide)).trans (hr2.mono (by decide))), by rw [e5]; rfl, ?_,
    fun j hj => ?_⟩
  · rw [hm2]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) v (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega)
  · rw [hm2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.outs j hj
    · rw [wd_write_self, hv]; rfl

end VG.Proof.X448.Arm

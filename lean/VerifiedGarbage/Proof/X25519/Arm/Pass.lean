import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.X25519.Arm

/-!
# X25519 on 32-bit ARM: carrying sums into limbs

`pass rb o src` stores at `[rb, #o]` the limbs of `Σ c_k 2^(16k) + cin`, from
the sums `c_k` that `src k` leaves in `r3` and the carry `cin` in `r5`
(`pass_ok`), for any `src` that computes them from the memory as it was, but
for the limbs already stored (`PassInv.frame`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm

theorem not_mem4 {r : Reg} (h : r ∉ [Reg.r2, .r3, .r4, .r5]) :
    r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

theorem carryStep_ok {rb : Reg} {off : Nat} {s : State} {a : Addr}
    (hrb : rb ≠ .r3 ∧ rb ≠ .r4) (ho : off < 4096)
    (ha : State.addr (s.gpr rb + BitVec.ofNat 32 off) = a) (hw : InRegions s.wr a 4)
    (h6 : s.gpr .r6 = mask16) (hs : (s.gpr .r3).toNat + (s.gpr .r5).toNat < 2 ^ 32) :
    WP isa (.block (carryStep rb off)) s fun s' =>
      (s'.gpr .r5).toNat = ((s.gpr .r3).toNat + (s.gpr .r5).toNat) / 65536 ∧
      (∃ v : BitVec 32, v.toNat = ((s.gpr .r3).toNat + (s.gpr .r5).toNat) % 65536 ∧
        s'.mem = s.mem.writeW a v) ∧
      Rest [.r3, .r4, .r5] s s' := by
  unfold carryStep
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_str (a := a) ho (by rw [u2.other _ hrb.2, u1.other _ hrb.1]; exact ha)
    (by rw [u2.wr, u1.wr]; exact hw) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = (s.gpr .r3).toNat + (s.gpr .r5).toNat := by
    rw [u1.gpr]; exact toNat_add_lt hs
  refine ⟨?_, ⟨s2.gpr .r4, ?_, ?_⟩, ?_⟩
  · rw [u4.gpr, u3.gpr, u2.other _ (by decide), toNat_shr, e1]
  · rw [u2.gpr, u1.other .r6 (by decide), h6]
    show (s1.gpr .r3 &&& mask16).toNat = _
    rw [toNat_and_mask16, e1]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · refine ⟨fun r hr => ?_, by rw [u4.rd, u3.rd, u2.rd, u1.rd], by rw [u4.wr, u3.wr, u2.wr, u1.wr],
      by rw [u4.sp, u3.sp, u2.sp, u1.sp]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.other _ hr.2.2, u3.gpr, u2.other _ hr.2.1, u1.other _ hr.1]

/-- After `k` limbs of `pass rb o src` from `s0`, for the sums `c` and the
carry `cin`. -/
structure PassInv (rb : Reg) (o : Nat) (s0 : State) (c : Nat → Nat) (cin k : Nat) (s : State) :
    Prop where
  rest : Rest [.r2, .r3, .r4, .r5] s0 s
  r5 : (s.gpr .r5).toNat = chain c cin k
  frame : Frame [⟨State.addr (s0.gpr rb) + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem (State.addr (s0.gpr rb)) (o + 4 * j) = out c cin j

theorem pass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.r2, .r3, .r4, .r5]) (ho : o + 64 ≤ 4096)
    (hfit : (s0.gpr rb).toNat + o + 64 ≤ 2 ^ 32)
    (hw : ∀ k < 16, InRegions s0.wr (State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k)) 4)
    (h6 : s0.gpr .r6 = mask16) (h5 : (s0.gpr .r5).toNat = cin)
    (hc : ∀ k < 16, c k + 65536 ≤ 2 ^ 32) (hcin : cin < 65536)
    (hsrc : ∀ k < 16, ∀ s, PassInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (pass rb o src)) s0 (PassInv rb o s0 c cin 16) := by
  have hr := not_mem4 hrb
  refine wp_range_flatMap (M := isa) (PassInv rb o s0 c cin) (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h5]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h3, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1, hr.2.2.1]), h.rest.gpr _ hrb]
  have h51 : s1.gpr .r5 = s.gpr .r5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (carryStep_ok (a := State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k))
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

end VG.Proof.X25519.Arm

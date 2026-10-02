import VerifiedGarbage.Proof.TripleDes.Arm.KeySteps
import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.Rc2.Arm.Lookup
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep)

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .r10 = (c.rotateLeft n).setWidth 32
  d : s'.gpr .r11 = (d.rotateLeft n).setWidth 32
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r4 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    WP isa (Impl.TripleDes.Arm.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.Arm.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, _, reg₁⟩ := rotate28_ok s .r10 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .r11 = d.setWidth 32 := (reg₁ .r11 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, _, reg₂⟩ := rotate28_ok s₁ .r11 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .r10 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 32 j >>> 1) == (0 : BitVec 32)) = decide (j < 2) ∧
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 k) == (0 : BitVec 32)) = decide (j = k) := by
  decide

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : s.gpr .r9 = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.mov .r4 (.shifted .r9 .lsr 1), .cmp .r4 (.imm 0)] s = some s' ∧
      isa.eval .eq s' = some (decide (j < 2)) ∧ Keep [.r4] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_⟩
  · change some (((s.gpr .r9 >>> 1) - 0) == 0) = _
    have hz : (s.gpr .r9 >>> 1) - (0 : BitVec 32) = s.gpr .r9 >>> 1 := by bv_omega
    rw [hz, hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [VG.Proof.Rc2.Arm.gpr_subFlags, gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .r9 = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.cmp .r9 (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      isa.eval .eq s' = some (decide (j = k)) ∧ Keep [.r4] s s' := by
  have henc : encodable (BitVec.ofNat 32 k) = true := by
    have hfinite : ∀ k < 16, encodable (BitVec.ofNat 32 k) = true := by decide
    exact hfinite k hk
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      henc, ite_true, Option.map_some]
    rfl, ?_, ?_⟩
  · change some ((s.gpr .r9 - BitVec.ofNat 32 k) == 0) = _
    rw [hv]
    exact congrArg some (comparison_values j hj k hk).2
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (hjreg : s.gpr .r9 = BitVec.ofNat 32 j) :
    WP isa Impl.TripleDes.Arm.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.Arm.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, keep₁⟩ := lowTest_ok s j hj hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.r4] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 5)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.Arm.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .r10 (by simp)).trans hc)
      ((h.reg .r11 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simpa only [List.mem_singleton] using ha))⟩
  have combine {a b : State} (ha : Keep [.r4] s a) (hb : Keep [.r4] a b) : Keep [.r4] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simpa only [h2, decide_true] using cond₁)
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simpa only [h2, decide_false] using cond₁)
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cond₂, keep₂⟩ := eqTest_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .r9 (by simp)).trans hjreg)
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      have keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simpa only [h8, decide_true] using cond₂)
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simpa only [h8, decide_false] using cond₂)
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cond₃, keep₃⟩ := eqTest_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .r9 (by simp)).trans hjreg)
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          have keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simpa only [h15, decide_true] using cond₃)
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simpa only [h15, decide_false] using cond₃)
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.Arm.Key

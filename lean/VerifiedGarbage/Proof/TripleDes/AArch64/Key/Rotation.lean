import VerifiedGarbage.Proof.TripleDes.AArch64.KeySteps
import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.Rc2.AArch64.Lookup

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .x19 = (c.rotateLeft n).setWidth 64
  d : s'.gpr .x20 = (d.rotateLeft n).setWidth 64
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .x4 → r ≠ .x19 → r ≠ .x20 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (Impl.TripleDes.AArch64.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.AArch64.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, _, reg₁⟩ := rotate28_ok s .x19 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .x20 = d.setWidth 64 := (reg₁ .x20 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, _, reg₂⟩ := rotate28_ok s₁ .x20 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .x19 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 64 j >>> 1) == (0 : BitVec 64)) = decide (j < 2) ∧
    ((BitVec.ofNat 64 j - BitVec.ofNat 64 k) == (0 : BitVec 64)) = decide (j = k) := by
  decide

theorem write_keep (s : State) (v : BitVec 64) : Keep [.x4] s (s.write .x .x4 v) := by
  refine ⟨?_, mem_write _ _ _ _, rd_write _ _ _ _, wr_write _ _ _ _⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  exact gpr_write_of_ne _ _ _ hr

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : s.gpr .x21 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.lsr .x .x4 .x21 1] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (decide (j < 2)) ∧ Keep [.x4] s s' := by
  refine ⟨s.write .x .x4 (s.gpr .x21 >>> 1), ?_, ?_, write_keep _ _⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (1 : Nat) < 64 from by decide, ite_true, State.read, BitVec.setWidth_eq]
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .x21 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.subImm .x .x4 .x21 k] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (decide (j = k)) ∧ Keep [.x4] s s' := by
  refine ⟨s.write .x .x4 (s.gpr .x21 - BitVec.ofNat 64 k), ?_, ?_, write_keep _ _⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show k < 4096 from by omega, ite_true, State.read, BitVec.setWidth_eq]
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (comparison_values j hj k hk).2

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64)
    (hjreg : s.gpr .x21 = BitVec.ofNat 64 j) :
    WP isa Impl.TripleDes.AArch64.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.AArch64.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, keep₁⟩ := lowTest_ok s j hj hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.x4] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 28)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.AArch64.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .x19 (by simp)).trans hc)
      ((h.reg .x20 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simpa only [List.mem_singleton] using ha))⟩
  have combine {a b : State} (ha : Keep [.x4] s a) (hb : Keep [.x4] a b) : Keep [.x4] s b :=
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
        ((keep₁.reg .x21 (by simp)).trans hjreg)
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
            ((keep₂'.reg .x21 (by simp)).trans hjreg)
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

end VG.Proof.TripleDes.AArch64.Key

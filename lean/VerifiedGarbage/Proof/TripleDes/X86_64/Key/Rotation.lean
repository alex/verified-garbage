import VerifiedGarbage.Proof.TripleDes.X86_64.KeySteps
import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.Rc2.X86_64.Lookup

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (Keep)

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .r12 = (c.rotateLeft n).setWidth 64
  d : s'.gpr .r13 = (d.rotateLeft n).setWidth 64
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (Impl.TripleDes.X86_64.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.X86_64.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, reg₁⟩ := rotate28_ok s .r12 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .r13 = d.setWidth 64 := (reg₁ .r13 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, reg₂⟩ := rotate28_ok s₁ .r13 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .r12 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    decide ((BitVec.ofNat 64 j).toNat < ((BitVec.ofNat 32 k).signExtend 64).toNat) = decide (j < k) ∧
    ((BitVec.ofNat 64 j - (BitVec.ofNat 32 k).signExtend 64) == (0 : BitVec 64)) = decide (j = k) := by
  decide

theorem cmp_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .r14 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.alu .cmp .r14 (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      s'.cf = some (decide (j < k)) ∧ s'.zf = some (decide (j = k)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_, ?_, ?_⟩
  · rw [cf_arithFlags, hv]
    exact congrArg some (comparison_values j hj k hk).1
  · rw [zf_arithFlags, hv]
    exact congrArg some (comparison_values j hj k hk).2
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64)
    (hjreg : s.gpr .r14 = BitVec.ofNat 64 j) :
    WP isa Impl.TripleDes.X86_64.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.X86_64.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cf₁, zf₁, keep₁⟩ := cmp_ok s j 2 hj (by decide) hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 28)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.X86_64.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .r12 (by simp)).trans hc)
      ((h.reg .r13 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simp))⟩
  have combine {a b : State} (ha : Keep [] s a) (hb : Keep [] a b) : Keep [] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simp only [eval, cf₁, h2, decide_true])
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simp only [eval, cf₁, h2, decide_false])
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cf₂, zf₂, keep₂⟩ := cmp_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .r14 (by simp)).trans hjreg)
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      have keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simp only [eval, zf₂, h8, decide_true])
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simp only [eval, zf₂, h8, decide_false])
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cf₃, zf₃, keep₃⟩ := cmp_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .r14 (by simp)).trans hjreg)
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          have keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simp only [eval, zf₃, h15, decide_true])
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simp only [eval, zf₃, h15, decide_false])
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.X86_64.Key

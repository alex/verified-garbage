import VerifiedGarbage.Proof.TripleDes.X86.Key.Rotation
import VerifiedGarbage.Proof.TripleDes.X86.RoundAdvance
import VerifiedGarbage.Proof.TripleDes.KeySchedule

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    decide ((BitVec.ofNat 32 j).toNat < (BitVec.ofNat 32 2).toNat) = decide (j < 2) ∧
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 k) == (0 : BitVec 32)) = decide (j = k) := by
  decide

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .ebp 20)), .alu .cmp .eax (.imm 2)] s = some s' ∧
      isa.eval .b s' = some (decide (j < 2)) ∧
      s'.gpr .eax = BitVec.ofNat 32 j ∧ Keep [.eax] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hok.slotIn 5 (by decide)
    exact ⟨r, List.mem_append_right _ h, hc⟩
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load32, State.ea, memOp, hr, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_⟩
  · change some (decide ((roundCount s).toNat < (BitVec.ofNat 32 2).toNat)) = _
    rw [hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1
  · exact hv
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .eax = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      isa.eval .e s' = some (decide (j = k)) ∧ s'.gpr .eax = BitVec.ofNat 32 j ∧ Keep [.eax] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some]
    rfl, ?_, ?_, ?_⟩
  · change some ((s.gpr .eax - BitVec.ofNat 32 k) == 0) = _
    rw [hv]
    exact congrArg some (comparison_values j hj k hk).2
  · exact hv
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (hjreg : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s) :
    WP isa Impl.TripleDes.X86.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.X86.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, eax₁, keep₁⟩ := lowTest_ok s j hj hjreg hok
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.eax] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 5)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.X86.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .esi (by simp)).trans hc)
      ((h.reg .edi (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    refine ⟨ht.c, ht.d, ⟨?_, ht.keep.mem.trans h.mem, ht.keep.rd.trans h.rd,
      ht.keep.wr.trans h.wr⟩⟩
    intro r hr
    have ha : r ∉ ([.eax] : List Reg) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact hr.2.2
    exact (ht.keep.reg r hr).trans (h.reg r ha)
  have combine {a b : State} (ha : Keep [.eax] s a) (hb : Keep [.eax] a b) : Keep [.eax] s b :=
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
      obtain ⟨s₂, run₂, cond₂, eax₂, keep₂⟩ := eqTest_ok s₁ j 8 hj (by decide)
        eax₁
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
          obtain ⟨s₃, run₃, cond₃, _, keep₃⟩ := eqTest_ok s₂ j 15 hj (by decide)
            eax₂
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

end VG.Proof.TripleDes.X86.Key

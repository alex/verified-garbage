import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

def countAddr (s : State) : Addr := s.gpr .rdx + BitVec.ofNat 64 56

theorem roundCountAdvance_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (countAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) :
    ∃ s', runBlock isa roundCountAdvance s = some s' ∧
      s'.mem = s.mem.writeW (countAddr s) (s.mem.readW (countAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (countAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  unfold countAddr at hread hwrite
  have hoff : BitVec.ofInt 64 (Int.ofNat 56) = BitVec.ofNat 64 56 := rfl
  refine ⟨_, by
    simp only [roundCountAdvance, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, memOp, hoff, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [zf_setReg, zf_arithFlags]
    rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

theorem pointerAdvance_ok (direction : Spec.TripleDes.Direction) (s : State) :
    ∃ s', runBlock isa
      [.alu (if direction = .encrypt then .add else .sub) .rdi (.imm 8)] s = some s' ∧
      s'.gpr .rdi = (if direction = .encrypt then s.gpr .rdi + 8 else s.gpr .rdi - 8) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) := by
  cases direction <;>
    refine ⟨_, by
      simp only [runBlock_cons, exec, execAlu, readSrc,
        Option.bind_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try exact gpr_setReg_self _ _ _
  all_goals try simp only [mem_setReg, mem_arithFlags]
  all_goals try simp only [rd_setReg, rd_arithFlags]
  all_goals try simp only [wr_setReg, wr_arithFlags]
  all_goals
    intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) == 0) = decide (n = 1) := by
  decide +kernel

theorem countWrite_frame (m : Mem) (p : Addr) (v : BitVec 64) :
    Frame [⟨p, 8⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

theorem roundAdvance_ok (direction : Spec.TripleDes.Direction) (s : State)
    (hread : InRegions (s.rd ++ s.wr) (countAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) :
    ∃ s', runBlock isa (roundAdvance direction) s = some s' ∧
      s'.gpr .rdi = (if direction = .encrypt then s.gpr .rdi + 8 else s.gpr .rdi - 8) ∧
      s'.mem = s.mem.writeW (countAddr s) (s.mem.readW (countAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (countAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, ptr₁, mem₁, rd₁, wr₁, keep₁⟩ := pointerAdvance_ok direction s
  have haddr : countAddr s₁ = countAddr s := by
    simp only [countAddr, keep₁ .rdx (by decide)]
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (countAddr s₁) 8 := by
    rw [rd₁, wr₁, haddr]; exact hread
  have hwrite₁ : InRegions s₁.wr (countAddr s₁) 8 := by
    rw [wr₁, haddr]; exact hwrite
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ := roundCountAdvance_ok s₁ hread₁ hwrite₁
  refine ⟨s₂, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩
  · simp only [roundAdvance, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .rdi (by decide)).trans ptr₁
  · rw [mem₂, mem₁, haddr]
  · rw [flag₂, mem₁, haddr]
  · exact fun r hrax hrdi => (keep₂ r hrax).trans (keep₁ r hrdi)

end VG.Proof.TripleDes.X86_64

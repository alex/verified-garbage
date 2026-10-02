import VerifiedGarbage.Proof.TripleDes.Arm.RoundBody
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (gpr_subFlags mem_subFlags)

def roundStepKept : List Reg := [.r1, .r2, .r3]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1)) ∧
    (!(BitVec.ofNat 32 n - 1 == 0)) = decide (n ≠ 1) := by decide +kernel

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = s.gpr .r9 - 1 ∧
      s'.z = ((s.gpr .r9 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r0 → s'.gpr r = s.gpr r) := by
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, ite_true, reduceCtorEq, ite_false, runBlock_cons,
      exec, Op2.eval, encodable, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    z_setReg, subFlags, rd_setReg, wr_setReg, sp_setReg, mem_setReg]
  all_goals try rfl
  all_goals
    intro r hr₁ hr₂
    simp only [hr₁, hr₂, ite_false]

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : keyWord s = k) (hok : Ok sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr .r9 = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, z₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := roundAdvance_ok d s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .r9 = BitVec.ofNat 32 n := (keep₁ .r9 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r10 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r11 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .r0 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.Arm.eval .ne s₂ = _
    simp only [VG.Arm.eval, z₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .r9 ∧ q ≠ .r0 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.Arm

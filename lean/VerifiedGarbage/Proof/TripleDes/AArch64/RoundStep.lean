import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def roundStepKept : List Reg := [.x0, .x1, .x2, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) != 0) = decide (n ≠ 1) := by
  decide +kernel

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.gpr .x22 = (if d = .encrypt then s.gpr .x22 + 8 else s.gpr .x22 - 8) ∧
      s'.gpr .x21 = s.gpr .x21 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, ite_true, reduceCtorEq, ite_false, runBlock_cons,
      runStep_some, runBlock_nil, exec, show (8 : Nat) < 4096 from by decide,
      show (1 : Nat) < 4096 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, gpr_write]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    try simp only [gpr_write, BitVec.setWidth_eq, rd_write, wr_write, sp_write, mem_write,
      reduceCtorEq, ite_true, ite_false]
  all_goals try rfl
  all_goals
    intro r hr₁ hr₂
    simp only [hr₁, hr₂, ite_false]

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .x19 = l.setWidth 64) (hr : s.gpr .x20 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .x22) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8)
    (hsep : (⟨s.gpr .x22, 8⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr .x21 = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .x19 = r.setWidth 64 ∧
      s'.gpr .x20 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .x22 = (if d = .encrypt then s.gpr .x22 + 8 else s.gpr .x22 - 8) ∧
      s'.gpr .x21 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero .x .x21) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := roundAdvance_ok d s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .x21 = BitVec.ofNat 64 n := (keep₁ .x21 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .x19 (by decide) (by decide)).trans left₁
  · exact (keep₂ .x20 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .x22 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.AArch64.eval (.nonzero .x .x21) s₂ = _
    simp only [VG.AArch64.eval, State.read, BitVec.setWidth_eq, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .x21 ∧ q ≠ .x22 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.AArch64

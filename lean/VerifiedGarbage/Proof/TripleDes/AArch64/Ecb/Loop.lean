import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.LoopFrame

/-! # Correctness of the ECB loop on complete blocks -/

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64
open VG.Proof.TripleDes (blocksAt_cons)

structure LoopPost (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * n)
  count : s'.gpr .x23 = 0
  reg : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x23 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .x23 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.TripleDes.blocksAt s'.mem (s.gpr .x1) n =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.TripleDes.blocksAt s.mem (s.gpr .x1) n)

theorem ecb_cons (keys : Spec.TripleDes.Schedule) (d : Spec.TripleDes.Direction)
    (b : Spec.TripleDes.Block) (bs : List Spec.TripleDes.Block) :
    Spec.TripleDes.ecb keys d (b :: bs) = blockResult keys d b :: Spec.TripleDes.ecb keys d bs := by
  cases d <;> rfl

theorem loop_ok (d : Spec.TripleDes.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 64 → StepPre s n → s.gpr .x23 = BitVec.ofNat 64 n →
      WP isa (.loop (.seq (Impl.TripleDes.AArch64.Ecb.blockCall d) (.block Impl.TripleDes.AArch64.Ecb.advance)) (.nonzero .x .x23)) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_⟩
        · rw [blocksAt_cons, blocksAt_cons, ecb_cons]
          simp only [Spec.TripleDes.blocksAt, List.range_zero, List.map_nil,
            Spec.TripleDes.ecb, List.map_nil]
          exact congrArg (· :: []) h₁.data
    · have hp₁ := h₁.tail hp
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega
        simp only [eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp bound
        have data := h₂.data
        have ki := h₁.reg .x0 (by decide) (by decide) (by decide)
        have bi := h₁.reg .x2 (by decide) (by decide) (by decide)
        rw [ki, h₁.ptr, key, tail] at data
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .x1 + ·) (by
            change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 64) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega) bi h₁.ptr)
        · have first := firstBlock_frame h₁ hp bound h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons, ecb_cons]

theorem maybeLoop_ok (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64)
    (hp : StepPre s n) (count : s.gpr .x23 = BitVec.ofNat 64 n)
    :
    WP isa (.ite (.zero .x .x23) (.block []) (.loop (.seq (Impl.TripleDes.AArch64.Ecb.blockCall d) (.block Impl.TripleDes.AArch64.Ecb.advance)) (.nonzero .x .x23))) s (LoopPost d s n) := by
  have flag' : zeroCount s = some (decide (n = 0)) := by
    rw [zeroCount, count, counter_zero n (by omega)]
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_⟩
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega) bound hp count


end VG.Proof.TripleDes.AArch64.Ecb

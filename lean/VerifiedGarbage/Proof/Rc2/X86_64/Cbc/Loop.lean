import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.LoopFrame

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (8 * n)
  count : s'.gpr .rbp = 0
  reg : ∀ r ∈ kept, r ≠ .rsi → r ≠ .rbp → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .rbp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (s.gpr .rsi) n =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blocksAt s.mem (s.gpr .rsi) n)).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .rbx) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blocksAt s.mem (s.gpr .rsi) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 64 → StepPre s n → s.gpr .rbp = BitVec.ofNat 64 n →
      WP isa (.loop (Impl.Rc2.X86_64.Cbc.body d) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_, ?_⟩
        · rw [blocksAt_cons, blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact congrArg (· :: []) h₁.data
        · rw [blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact h₁.iv
    · have hp₁ := h₁.tail hp
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega
        simp only [eval, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp bound
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .rdi (by decide) (by decide) (by decide)
        have vi := h₁.reg .rbx (by decide) (by decide) (by decide)
        have bi := h₁.reg .rdx (by decide) (by decide) (by decide)
        have sp := h₁.reg .rsp (by decide) (by decide) (by decide)
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at data
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .rsi + ·) (by
            change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 64) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega) vi bi sp h₁.ptr)
        · have first := firstBlock_frame h₁ hp bound h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64)
    (hp : StepPre s n) (count : s.gpr .rbp = BitVec.ofNat 64 n)
    (flag : s.zf = some (s.gpr .rbp == 0)) :
    WP isa (.ite .e (.block []) (.loop (Impl.Rc2.X86_64.Cbc.body d) .ne)) s (LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : s.zf = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 8 ≤ 512) :
    s'.mem.readW (s.gpr .rdx + BitVec.ofNat 64 i) 64 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 i) 64 := by
  have sub : Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 i, 8⟩ (bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (s.gpr .rdx + BitVec.ofNat 64 i) 8).Disjoint ⟨s.gpr .rdx, 264⟩ :=
    Offset.disjoint_base _ lo (by omega)
  apply h.mem.readW (r := ⟨s.gpr .rdx + BitVec.ofNat 64 i, 8⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      (And.intro sep ((hp.stackBuf.sub_right sub).symm)))

end VG.Proof.Rc2.X86_64.Cbc

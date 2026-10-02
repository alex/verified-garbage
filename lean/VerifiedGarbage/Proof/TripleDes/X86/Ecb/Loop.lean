import VerifiedGarbage.Proof.TripleDes.X86.Ecb.LoopFrame

/-! # Correctness of the ECB loop on complete blocks -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)
open VG.Proof.TripleDes (blocksAt_cons)

structure LoopPost (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .edi = 0
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.TripleDes.blocksAt s'.mem (addr32 (s.gpr .esi)) n =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.TripleDes.blocksAt s.mem (addr32 (s.gpr .esi)) n)

theorem ecb_cons (keys : Spec.TripleDes.Schedule) (d : Spec.TripleDes.Direction)
    (b : Spec.TripleDes.Block) (bs : List Spec.TripleDes.Block) :
    Spec.TripleDes.ecb keys d (b :: bs) = blockResult keys d b :: Spec.TripleDes.ecb keys d bs := by
  cases d <;> rfl

theorem loop_ok (d : Spec.TripleDes.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .edi = BitVec.ofNat 32 n →
      WP isa (.loop (.seq (Impl.TripleDes.X86.Ecb.blockCall d) (.block Impl.TripleDes.X86.Ecb.advance)) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · change isa.eval .ne s₁ = some false
        simpa only [Nat.zero_add, Nat.lt_irrefl, decide_false] using h₁.flag
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.rd, h₁.wr, h₁.frame (by decide), ?_⟩
        · rw [blocksAt_cons, blocksAt_cons, ecb_cons]
          simp only [Spec.TripleDes.blocksAt, List.range_zero, List.map_nil,
            Spec.TripleDes.ecb, List.map_nil]
          exact congrArg (· :: []) h₁.data
    · have hp₁ := h₁.tail hp (by omega)
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · change isa.eval .ne s₁ = some true
        simpa only [show 1 < n + 1 by omega, decide_true] using h₁.flag
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega_using [bound])
        have data := h₂.data
        have ki := h₁.reg .ebx (by decide) (by decide) (by decide)
        have bi := h₁.reg .ebp (by decide) (by decide) (by decide)
        have ptrAddr : addr32 (s₁.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
          rw [h₁.ptr]
          exact addr_add (k := 8) (by omega_using [hp.dataFit, hz])
        rw [ki, ptrAddr, key, tail] at data
        refine ⟨?_, h₂.count, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .esi + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega) (by omega_using [hp.dataFit, hz]) bi (h₁.reg .esp (by decide) (by decide) (by decide)) h₁.ptr)
        · have first := firstBlock_frame h₁ hp (by omega_using [bound]) h₂.mem (by omega)
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons, ecb_cons]

theorem maybeLoop_ok (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .edi = BitVec.ofNat 32 n)
    (initialFlag : isa.eval .e s = some (decide (n = 0)))
    :
    WP isa (.ite .e (.block []) (.loop (.seq (Impl.TripleDes.X86.Ecb.blockCall d) (.block Impl.TripleDes.X86.Ecb.advance)) .ne)) s (LoopPost d s n) := by
  have flag' := initialFlag
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by change isa.eval .e s = some true; simpa only [decide_true] using flag')
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_⟩
      · rfl
    · simp
  · apply WP.ite false (by change isa.eval .e s = some false; simpa only [hz, decide_false] using flag')
    · simp
    · intro _
      exact loop_ok d n s (by omega) bound hp count


end VG.Proof.TripleDes.X86.Ecb

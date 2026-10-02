import VerifiedGarbage.Proof.TripleDes.X86.RoundAdvance

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def workRegion (s : State) : Region := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 16, 432⟩

theorem spill_sub_work (s : State) : Region.Sub (spillRegion s) (workRegion s) :=
  Offset.sub _ (by decide) (by decide)

theorem count_spill_disjoint (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    (⟨wordAddr (s.gpr .ebp) 5, 4⟩ : Region).Disjoint (spillRegion s) := by
  change (⟨addr (s.gpr .ebp) 20, 4⟩ : Region).Disjoint (spillRegion s)
  rw [addr_eq (by omega)]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem advance_frame (d : Spec.TripleDes.Direction) (s : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Frame [workRegion s] s.mem (advanceMem d s) := by
  have h4 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h5 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h4).writeW
    (List.mem_singleton_self _) _ h5

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1)) ∧
    (!(BitVec.ofNat 32 n - 1 == 0)) = decide (n ≠ 1) := by decide +kernel

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .esi = l) (hr : s.gpr .edi = r) (hk : roundKeyWord s = k)
    (pre : BoxPre s) (hcount : roundCount s = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .esi = r ∧ s'.gpr .edi = l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) ∧
      roundKeyPtr s' = nextPtr d s ∧ roundCount s' = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [workRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, base₁, sp₁, frame₁⟩ := roundBody_ok s l r k hl hr hk pre
  obtain ⟨pre₁, _⟩ := pre.frame base₁ rd₁ wr₁ frame₁
  have ptr₁ := roundKeyPtr_frame pre base₁ frame₁
  have count₁ : roundCount s₁ = roundCount s := by
    unfold roundCount
    rw [base₁]
    exact frame₁.readW (r := ⟨wordAddr (s.gpr .ebp) 5, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact count_spill_disjoint s pre.scratch.fit)
      (by decide)
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ := roundAdvance_ok d s₁ pre₁.scratch
  have base₂ : s₂.gpr .ebp = s₁.gpr .ebp := keep₂ _ (by decide)
  have ptr₂ : roundKeyPtr s₂ = nextPtr d s₁ := by
    unfold roundKeyPtr
    rw [base₂, mem₂]
    have hsep : Mem.Sep (wordAddr (s₁.gpr .ebp) 4) 4 (wordAddr (s₁.gpr .ebp) 5) 4 := by
      intro a h4 h5
      exact counter_ptr_sep s₁ pre₁.scratch.fit a h5 h4
    rw [advanceMem, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32]
  have count₂ : roundCount s₂ = BitVec.ofNat 32 (n - 1) := by
    unfold roundCount
    rw [base₂, mem₂, advanceMem, Mem.readW_writeW_self32, count₁, hcount,
      (countDown_rules n hn' hn).1]
  refine ⟨s₂, ?_, (keep₂ .esi (by decide)).trans left₁,
    (keep₂ .edi (by decide)).trans right₁, ?_, count₂, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    base₂.trans base₁, (keep₂ .esp (by decide)).trans sp₁, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · rw [ptr₂]; simp only [nextPtr, ptr₁]
  · change VG.X86.eval .ne s₂ = _
    simp only [VG.X86.eval, flag₂, count₁, hcount, Option.map_some, (countDown_rules n hn' hn).2]
  · have hf₁ : Frame [workRegion s] s.mem s₁.mem := frame₁.sub (by
      intro q hq; obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, spill_sub_work s⟩)
    have hf₂ := advance_frame d s₁ pre₁.scratch.fit
    have hwork : workRegion s₁ = workRegion s := by simp only [workRegion, base₁]
    rw [hwork, ← mem₂] at hf₂
    exact hf₁.trans hf₂
end VG.Proof.TripleDes.X86

import VerifiedGarbage.Proof.TripleDes.X86_64.PassSteps

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64

def workRegion (s : State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 56, 392⟩

theorem count_spill_disjoint (s : State) :
    (⟨countAddr s, 8⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem spill_sub_work (s : State) : Region.Sub (spillRegion s) (workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem count_sub_work (s : State) : Region.Sub ⟨countAddr s, 8⟩ (workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem roundStep_ok (direction : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r12 = l.setWidth 64) (hr : s.gpr .r13 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .rdi) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8)
    (hsep : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.mem.readW (countAddr s) 64 = BitVec.ofNat 64 n)
    (hcountRead : InRegions (s.rd ++ s.wr) (countAddr s) 8)
    (hcountWrite : InRegions s.wr (countAddr s) 8) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance direction) s = some s' ∧
      s'.gpr .r12 = r.setWidth 64 ∧
      s'.gpr .r13 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .rdi = (if direction = .encrypt then s.gpr .rdi + 8 else s.gpr .rdi - 8) ∧
      s'.mem.readW (countAddr s') 64 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.rsi, .rdx, .rsp], s'.gpr q = s.gpr q) ∧
      Frame [workRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  have haddr : countAddr s₁ = countAddr s := by
    simp only [countAddr, keep₁ .rdx (by decide)]
  have hcount₁ : s₁.mem.readW (countAddr s₁) 64 = BitVec.ofNat 64 n := by
    rw [haddr]
    refine Eq.trans (frame₁.readW (r := ⟨countAddr s, 8⟩) ?_ ?_ (by decide)) hcount
    · exact Region.contains_self _ _
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact count_spill_disjoint s
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (countAddr s₁) 8 := by
    rw [rd₁, wr₁, haddr]; exact hcountRead
  have hwrite₁ : InRegions s₁.wr (countAddr s₁) 8 := by
    rw [wr₁, haddr]; exact hcountWrite
  obtain ⟨s₂, run₂, ptr₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ :=
    roundAdvance_ok direction s₁ hread₁ hwrite₁
  have hcountAddr₂ : countAddr s₂ = countAddr s₁ := by
    simp only [countAddr, keep₂ .rdx (by decide) (by decide)]
  have hwork : workRegion s₁ = workRegion s := by
    simp only [workRegion, keep₁ .rdx (by decide)]
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r12 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r13 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .rdi (by decide)]
  · rw [hcountAddr₂, mem₂, Mem.readW_writeW_self64, hcount₁, hsub]
  · change VG.X86_64.eval .ne s₂ = some (decide (n ≠ 1))
    simp only [VG.X86_64.eval, flag₂, hcount₁, hzero, Option.map_some]
    simp
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .rax ∧ q ≠ .rdi := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · have hf₁ : Frame [workRegion s] s.mem s₁.mem := frame₁.sub (by
      intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, spill_sub_work s⟩)
    have hf₂ := countWrite_frame s₁.mem (countAddr s₁) (s₁.mem.readW (countAddr s₁) 64 - 1)
    have hf₂' : Frame [workRegion s₁] s₁.mem s₂.mem := by
      rw [mem₂]
      exact hf₂.sub (by
        intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact ⟨_, List.mem_singleton_self _, count_sub_work s₁⟩)
    rw [hwork] at hf₂'
    exact hf₁.trans hf₂'

end VG.Proof.TripleDes.X86_64

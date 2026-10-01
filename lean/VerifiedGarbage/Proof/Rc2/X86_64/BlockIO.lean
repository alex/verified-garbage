import VerifiedGarbage.Proof.Rc2.X86_64.Cipher
import VerifiedGarbage.Proof.Rc2.Memory

/-! # Loading and storing RC2 blocks -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem unpackWord_ok (s : State) (i : Nat) (hi : i < 4) :
    ∃ s', runBlock isa (unpackWord i) s = some s' ∧
      s'.gpr (wordReg i) = (((s.gpr .rax) >>> (16 * i)).setWidth 16).setWidth 64 ∧
      Keep [wordReg i] s s' := by
  by_cases hz : i = 0
  · subst i
    refine ⟨_, by
      simp only [unpackWord, rr, ite_true, List.append_nil, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
        Option.map_some, Option.bind_some, gpr_setReg, ite_true]
      rfl, ?_⟩
    constructor
    · simp only [gpr_setReg_self, Nat.mul_zero, BitVec.ushiftRight_zero]
      exact maskWord _
    · constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags]
      · simp only [rd_setReg, rd_arithFlags]
      · simp only [wr_setReg, wr_arithFlags]
  · have hn : 1 ≤ 16 * i ∧ 16 * i ≤ 63 := by omega
    refine ⟨_, by
      simp only [unpackWord, rr, hz, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
        Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags, hn, and_self, ite_true]
      rfl, ?_⟩
    constructor
    · rw [gpr_setReg_self]
      exact maskWord _
    · constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
      · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
      · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem unpackWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State) :
    WP isa (.block (is.flatMap unpackWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) = (((s.gpr .rax) >>> (16 * i)).setWidth 16).setWidth 64) ∧
      Keep (is.map wordReg) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := unpackWord_ok s i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁)
    intro s₂ h₂
    have input₁ := keep₁.reg .rax (by
      simp only [List.mem_singleton]
      exact Ne.symm (wordReg_separate i).1)
    constructor
    · intro j hj
      rw [List.mem_cons] at hj
      by_cases hm : j ∈ is
      · rw [h₂.1 j hm, input₁]
      · have he : j = i := hj.resolve_right hm
        subst j
        rw [h₂.2.reg _ (by
          intro hm'
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
          have je := (wordReg_injective j (hi j (List.mem_cons_of_mem _ hj)) i (hi i (by simp))).mp he
          exact hm (je ▸ hj)), out₁]
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem blockLoad_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    WP isa (.block blockLoad) s (fun s' =>
      Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .rsi))) ∧
      Keep roundWrites s s') := by
  rw [blockLoad, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.mem.readW (s.gpr .rsi) 64)
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, State.ea, offset_nat, BitVec.add_zero, readable, ite_true,
      Option.map_some]
    rfl
  apply WP.mono (unpackWords_ok (List.range 4) (fun i hi => List.mem_range.mp hi) s₁)
  intro s₂ h₂
  constructor
  · intro i hi
    rw [h₂.1 i (List.mem_range.mpr hi), decode_read64 _ _ i hi]
    rfl
  · have keep₁ : Keep roundWrites s s₁ := by
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ (by decide)))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _
    apply keep₁.trans
    exact h₂.2.weaken (by
      intro r hr
      obtain ⟨i, _, he⟩ := List.mem_map.mp hr
      subst r; exact wordReg_mem_roundWrites i)

theorem packWord_ok (s : State) (i : Nat) (hi : 1 ≤ i) (hi' : i < 4) :
    ∃ s', runBlock isa (packWord i) s = some s' ∧
      s'.gpr .rax = s.gpr .rax ||| (s.gpr (wordReg i)).rotateRight (64 - 16 * i) ∧
      Keep [.rax, .rcx] s s' := by
  have hn : 1 ≤ 64 - 16 * i ∧ 64 - 16 * i ≤ 63 := by omega
  refine ⟨_, by
    simp only [packWord, rr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      execShift, readSrc, Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags,
      hn, and_self, reduceCtorEq, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem packWords_ok (is : List Nat) (hi : ∀ i ∈ is, 1 ≤ i ∧ i < 4)
    (s : State) (v : Spec.Rc2.State) (hv : Words s v) :
    WP isa (.block (is.flatMap packWord)) s (fun s' =>
      s'.gpr .rax = is.foldl (fun acc i => acc |||
        ((v.getD i 0).setWidth 64).rotateRight (64 - 16 * i)) (s.gpr .rax) ∧
      Keep [.rax, .rcx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := packWord_ok s i bound.1 bound.2
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have keepTemps : Keep temps s s₁ := keep₁.weaken (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h <;> subst r <;> decide)
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ (hv.preserve keepTemps))
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, hv i bound.2]
    rfl

/-- The block store changes exactly the data word, plus two caller-saved
registers; it leaves all memory-access permissions unchanged. -/
theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (writable : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (.block blockStore) s (fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi) (pack v) ∧
      (∀ r, r ∉ [.rax, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr) := by
  rw [blockStore, List.append_assoc, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.gpr (wordReg 0))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : Keep [.rax, .rcx] s s₁ := by
    constructor
    · intro r hr
      exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _
  have keepTemps : Keep temps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h <;> subst r <;> decide)
  apply WP.mono (packWords_ok [1, 2, 3] (by decide) s₁ v (hv.preserve keepTemps))
  intro s₂ h₂
  have keep := keep₁.trans h₂.2
  have ptr₂ := keep.reg .rsi (by decide)
  have out₂ : s₂.gpr .rax = pack v := by
    rw [h₂.1]
    change ((s.gpr (wordReg 0) ||| ((v.getD 1 0).setWidth 64).rotateRight 48) |||
      ((v.getD 2 0).setWidth 64).rotateRight 32) |||
      ((v.getD 3 0).setWidth 64).rotateRight 16 = _
    rw [hv 0 (by decide)]
    exact (pack_eq v).symm
  refine WP.of_runBlock ⟨{s₂ with mem := s₂.mem.writeW (s₂.gpr .rsi) (s₂.gpr .rax)}, ?_, ?_⟩
  · have valid : InRegions s₂.wr (s₂.gpr .rsi) 8 := by rw [keep.wr, ptr₂]; exact writable
    simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
      State.ea, offset_nat, BitVec.add_zero, valid, ite_true]
  · exact ⟨by rw [keep.mem, ptr₂, out₂], keep.reg, keep.rd, keep.wr⟩

end VG.Proof.Rc2.X86_64

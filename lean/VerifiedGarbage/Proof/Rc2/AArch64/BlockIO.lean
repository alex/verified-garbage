import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.AArch64.MemOps

/-! # Loading and storing RC2 blocks -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem unpackWord_ok (s : State) (i : Nat) (hi : i < 4) :
    ∃ s', runBlock isa (unpackWord i) s = some s' ∧
      s'.gpr (wordReg i) = (((s.gpr .x8) >>> (16 * i)).setWidth 16).setWidth 64 ∧
      Keep [wordReg i] s s' := by
  have hn : 16 * i < 64 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [unpackWord, mask, rr, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, gpr_write, BitVec.setWidth_eq,
      hn, ite_true, BitVec.add_zero]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq]
    exact maskBits _ 16 (by decide)
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem unpackWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State) :
    WP isa (.block (is.flatMap unpackWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) = (((s.gpr .x8) >>> (16 * i)).setWidth 16).setWidth 64) ∧
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
    have input₁ := keep₁.reg .x8 (by
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
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8) :
    WP isa (.block blockLoad) s (fun s' =>
      Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1))) ∧
      Keep roundWrites s s') := by
  rw [blockLoad, WP.block_append_iff]
  let s₁ := s.write .x .x8 (s.mem.readW (s.gpr .x1) 64)
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [runBlock_cons, exec_ldr_x _ _ _ 0 (by decide) (by simpa using readable),
      runStep_some, runBlock_nil, BitVec.add_zero]
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
        exact gpr_write_of_ne _ _ _ (fun he => hr (he ▸ (by decide)))
      · exact mem_write _ _ _ _
      · exact rd_write _ _ _ _
      · exact wr_write _ _ _ _
    apply keep₁.trans
    exact h₂.2.weaken (by
      intro r hr
      obtain ⟨i, _, he⟩ := List.mem_map.mp hr
      subst r; exact wordReg_mem_roundWrites i)

theorem packWord_ok (s : State) (i : Nat) (hi : 1 ≤ i) (hi' : i < 4) :
    ∃ s', runBlock isa (packWord i) s = some s' ∧
      s'.gpr .x8 = s.gpr .x8 ||| (s.gpr (wordReg i)).rotateRight (64 - 16 * i) ∧
      Keep [.x8, .x3] s s' := by
  have hn : 64 - 16 * i < 64 := by omega
  refine ⟨_, by
    simp only [packWord, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, BitVec.setWidth_eq, gpr_write, BitVec.setWidth_eq,
      hn, reduceCtorEq, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_write_self _ _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem packWords_ok (is : List Nat) (hi : ∀ i ∈ is, 1 ≤ i ∧ i < 4)
    (s : State) (v : Spec.Rc2.State) (hv : Words s v) :
    WP isa (.block (is.flatMap packWord)) s (fun s' =>
      s'.gpr .x8 = is.foldl (fun acc i => acc |||
        ((v.getD i 0).setWidth 64).rotateRight (64 - 16 * i)) (s.gpr .x8) ∧
      Keep [.x8, .x3] s s') := by
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
    (writable : InRegions s.wr (s.gpr .x1) 8) :
    WP isa (.block blockStore) s (fun s' =>
      s'.mem = s.mem.writeW (s.gpr .x1) (pack v) ∧
      (∀ r, r ∉ [.x8, .x3] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr) := by
  rw [blockStore, List.append_assoc, WP.block_append_iff]
  let s₁ := s.write .x .x8 (s.gpr (wordReg 0))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, BitVec.setWidth_eq, BitVec.add_zero, show 0 < 4096 by decide, ite_true]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : Keep [.x8, .x3] s s₁ := by
    constructor
    · intro r hr
      exact gpr_write_of_ne _ _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_write _ _ _ _
    · exact rd_write _ _ _ _
    · exact wr_write _ _ _ _
  have keepTemps : Keep temps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h <;> subst r <;> decide)
  apply WP.mono (packWords_ok [1, 2, 3] (by decide) s₁ v (hv.preserve keepTemps))
  intro s₂ h₂
  have keep := keep₁.trans h₂.2
  have ptr₂ := keep.reg .x1 (by decide)
  have out₂ : s₂.gpr .x8 = pack v := by
    rw [h₂.1]
    change ((s.gpr (wordReg 0) ||| ((v.getD 1 0).setWidth 64).rotateRight 48) |||
      ((v.getD 2 0).setWidth 64).rotateRight 32) |||
      ((v.getD 3 0).setWidth 64).rotateRight 16 = _
    rw [hv 0 (by decide)]
    exact (pack_eq v).symm
  refine WP.of_runBlock ⟨{s₂ with mem := s₂.mem.writeW (s₂.gpr .x1) (s₂.gpr .x8)}, ?_, ?_⟩
  · have valid : InRegions s₂.wr (s₂.gpr .x1) 8 := by rw [keep.wr, ptr₂]; exact writable
    simp only [runBlock_cons, exec_str_x _ _ _ 0 (by decide) (by simpa using valid),
      runStep_some, runBlock_nil, BitVec.add_zero]
  · exact ⟨by rw [keep.mem, ptr₂, out₂], keep.reg, keep.rd, keep.wr⟩

end VG.Proof.Rc2.AArch64

import VerifiedGarbage.Proof.Rc2.Arm.Cipher
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-! # Byte loads and stores for RC2 on ARMv7 -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm

theorem decode_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  rw [Spec.Rc2.decodeBlock, getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  rw [Spec.Rc2.blockAt, getD_ofFn _ _ (by omega), getD_ofFn _ _ (by omega)]

theorem loadWord_ok (s : State) (i : Nat) (hi : i < 4)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (loadWord i) s = some s' ∧
      s'.gpr (wordReg i) =
        ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).getD i 0).setWidth 32 ∧
      Keep [wordReg i, .r12] s s' := by
  have sep := wordReg_separate i
  have lo := readable (2 * i) (by omega)
  have high := readable (2 * i + 1) (by omega)
  have a := addr_add (a := s.gpr .r1) (k := 2 * i) (by omega)
  have b := addr_add (a := s.gpr .r1) (k := 2 * i + 1) (by omega)
  have loOff : 2 * i < 4096 := by omega
  have hiOff : 2 * i + 1 < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [loadWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.load8, loOff, hiOff, a, b, lo, high, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      Ne.symm sep.2.2.2.2.1, sep.1, Ne.symm sep.1, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, sep.1, ite_false, ite_true]
    rw [decode_word _ _ i hi]
    exact Word32.joinBytes_shift _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem loadWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block (is.flatMap loadWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) =
        ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).getD i 0).setWidth 32) ∧
      Keep (is.map wordReg ++ ([.r12] : List Reg)) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := loadWord_ok s i (hi i (by simp)) fit readable
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have ptr₁ := keep₁.reg .r1 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Ne.symm (wordReg_separate i).2.2.2.2.1, by decide⟩)
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁
      (by rw [ptr₁]; exact fit) (by rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable))
    intro s₂ h₂
    constructor
    · intro j hj
      rw [List.mem_cons] at hj
      by_cases hm : j ∈ is
      · rw [h₂.1 j hm, keep₁.mem, ptr₁]
      · have he : j = i := hj.resolve_right hm
        subst j
        rw [h₂.2.reg _ (by
          simp only [List.mem_append, List.mem_singleton, not_or]
          refine ⟨?_, (wordReg_separate i).1⟩
          intro hm'
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
          have je := (wordReg_injective j (hi j (List.mem_cons_of_mem _ hj)) i (hi i (by simp))).mp he
          exact hm (je ▸ hj)), out₁]
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h
        · subst r; simp
        · subst r; simp
      · exact List.mem_cons_of_mem _ hr

theorem blockLoad_ok (s : State) (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block blockLoad) s (fun s' =>
      Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))) ∧
      Keep roundWrites s s') := by
  apply WP.mono (loadWords_ok (List.range 4) (fun i hi => List.mem_range.mp hi) s fit readable)
  intro s' h
  refine ⟨fun i hi => h.1 i (List.mem_range.mpr hi), h.2.weaken ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, _, he⟩ := List.mem_map.mp hr
    subst r; exact wordReg_mem_roundWrites i
  · simp only [List.mem_singleton] at hr
    subst r; decide

end VG.Proof.Rc2.Arm

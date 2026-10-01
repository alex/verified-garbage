import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure EntryStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r

theorem EntryStep.refl (s : State) : EntryStep s s := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
theorem EntryStep.trans {s t u : State} (h : EntryStep s t) (h' : EntryStep t u) : EntryStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r hn hl => (h'.regs r hn hl).trans (h.regs r hn hl)⟩

theorem argReg_ne12 (j : Nat) : argReg j ≠ .r12 := by unfold argReg; split <;> decide
theorem argReg_neLR (j : Nat) : argReg j ≠ .lr := by unfold argReg; split <;> decide

def inputWord (s : State) (j : Nat) : BitVec 32 :=
  if j < 4 then s.gpr (argReg j)
  else s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 32

theorem saveWord_ok {s : State} {j : Nat} (hj : j < 6)
    (hw : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 (248 + 4 * j))) 4)
    (hr : 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4) :
    WP isa (.block (saveWord j)) s fun t => EntryStep s t ∧
      t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 (248 + 4 * j))) (inputWord s j) := by
  have hs : 4 * j < 4096 := by omega
  have ha : BitVec.ofNat 32 248 + BitVec.ofNat 32 (4 * j) = BitVec.ofNat 32 (248 + 4 * j) :=
    (BitVec.ofNat_add 248 (4 * j)).symm
  by_cases h4 : j < 4
  · apply WP.of_runBlock
    simp only [saveWord, ite_true, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.store32, Nat.reduceLT, hs, ite_true, RegUpd.gpr_setReg, RegUpd.wr_setReg,
      RegUpd.mem_setReg, RegUpd.sp_setReg, argReg_ne12, ite_false, BitVec.add_assoc, ha,
      hw, Option.some.injEq, exists_eq_left', inputWord, h4, ite_true]
    refine ⟨⟨rfl, rfl, rfl, ?_⟩, True.intro⟩
    intro r hn _
    simp only [RegUpd.gpr_setReg, hn, ite_false]
  · have hl : 280 + 4 * (j - 4) < 4096 := by omega
    have hr' := hr (by omega)
    apply WP.of_runBlock
    simp only [saveWord, ite_false, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
      Nat.reduceLT, reduceCtorEq, hs, hl, ite_true, hr', Option.map_some, RegUpd.gpr_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.sp_setReg, BitVec.add_assoc, ha,
      hw, Option.some.injEq, exists_eq_left', inputWord, h4, ite_false]
    refine ⟨⟨rfl, rfl, rfl, ?_⟩, True.intro⟩
    intro r hn hlr
    simp only [RegUpd.gpr_setReg, hn, hlr, ite_false]

structure Saved (s : State) (n : Nat) (t : State) : Prop where
  step : EntryStep s t
  frame : Frame [⟨State.addr s.sp + 248, 24⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr s.sp + BitVec.ofNat 64 (248 + 4 * j)) 32 = inputWord s j

theorem Saved.input_word {s t : State} {n j : Nat} (h : Saved s n t)
    (_hj : j < 6) (hf : s.sp.toNat + 280 + 4 * (j - 4) < 2 ^ 32) : inputWord t j = inputWord s j := by
  unfold inputWord
  split
  · exact h.step.regs _ (argReg_ne12 _) (argReg_neLR _)
  · rw [h.step.sp]
    refine h.frame.readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4))), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr, addr_add (by omega)]
    exact Offset.disjoint _ (d := 280 + 4 * (j - 4)) (e := 248)
      (by omega) (by omega) (by omega)

theorem saveArgs_ok {s : State} : ∀ n ≤ 6,
    s.sp.toNat + 280 + 4 * (n - 4) ≤ 2 ^ 32 →
    (⟨State.addr s.sp + 248, 24⟩ : Region) ∈ s.wr →
    (∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4) →
    WP isa (.block (saveArgs n)) s (Saved s n)
  | 0, _, _, _, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn, hf, hw, hr => by
    rw [saveArgs, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (saveArgs_ok n (by omega) (by omega) hw (fun j hj => hr j (by omega))) fun u hu => ?_
    have he : State.addr (u.sp + BitVec.ofNat 32 (248 + 4 * n)) =
        State.addr s.sp + BitVec.ofNat 64 (248 + 4 * n) := by
      rw [hu.step.sp, addr_add (by omega)]
    have uw : InRegions u.wr (State.addr (u.sp + BitVec.ofNat 32 (248 + 4 * n))) 4 := by
      rw [he, hu.step.wr]
      exact ⟨_, hw, Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
    have ur : 4 ≤ n → InRegions (u.rd ++ u.wr)
        (State.addr (u.sp + BitVec.ofNat 32 (280 + 4 * (n - 4)))) 4 := by
      intro h4
      rw [hu.step.sp, hu.step.rd, hu.step.wr]
      exact hr n (by omega) h4
    refine WP.mono (saveWord_ok (by omega) uw ur) fun t ⟨ht, mt⟩ => ?_
    have hi : inputWord u n = inputWord s n := by
      by_cases h4 : n < 4
      · simp only [inputWord, h4, ite_true]
        exact hu.step.regs _ (argReg_ne12 _) (argReg_neLR _)
      · exact hu.input_word (by omega) (by omega)
    rw [he, hi] at mt
    refine ⟨hu.step.trans ht, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

end VG.Proof.Ed25519.Arm.Whole

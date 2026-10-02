import VerifiedGarbage.Impl.Argon2.X86_64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillContext

/-! Select index two only in slice zero of pass zero. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

def start (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem start_active (pass slice : Nat) : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start pass slice := by
  unfold start; split <;> omega

theorem start_le (pass slice : Nat) (g : Nat) (minimum : 2 ≤ g) : start pass slice ≤ g := by
  unfold start; split <;> omega

theorem first_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block first) s fun t =>
      t.zf = decide (s.mem.readW (off (s.gpr .rbp) 0) 64 = 0#64 ∧ s.gpr .r14 = 0#64) ∧
      Divide.Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [first, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change ((s.mem.readW (off (s.gpr .rbp) 0) 64 ||| s.gpr .r14) - 0#64 == 0#64) = _
    rw [BitVec.sub_zero]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem register_ok (s : State) (register : Reg) (value : BitVec 32) :
    WP isa (.block [.mov register (.imm value)]) s fun t =>
      t.gpr register = value.signExtend 64 ∧ Divide.Keeps [register] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem index_ok (s : State) (pass slice : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) : WP isa index s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (start pass slice) ∧ Divide.Keeps [.rcx, .r15] s t := by
  unfold index
  refine WP.seq ((first_ok s hr).mono ?_)
  rintro a ⟨flag, keeps⟩
  have firstFlag : a.zf = decide (pass = 0 ∧ slice = 0) := by
    rw [flag, passWord, sliceWord]
    have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
    have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 := ReferenceMap.word_zero slice sliceBound
    simp only [passZero, sliceZero]
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) (by simp only [eval, firstFlag]) ?_ ?_
  · intro mode
    refine (register_ok a .r15 2).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_true mode]; exact value
  · intro mode
    refine (register_ok a .r15 0).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_false mode, ite_false]; exact value

theorem check_ok (s : State) : WP isa (.block check) s fun t =>
    t.cf = decide ((s.gpr .r15).toNat < (s.gpr .r13).toNat) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [check, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.cf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

end VG.Proof.Argon2.X86_64.SegmentSetup

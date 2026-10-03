import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState
import VerifiedGarbage.Impl.Argon2.AArch64.FirstLane
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceLane
import VerifiedGarbage.Proof.Argon2.AArch64.Divide
import VerifiedGarbage.Proof.Argon2.AArch64.DivideCT

/-! Merged from `Proof.Argon2.AArch64.ReferenceLane`. -/
section
/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.AArch64.ReferenceLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceLane
open VG.Impl.Argon2.AArch64

structure Prefix (s t : State) : Prop where
  high : t.gpr .x0 = s.gpr .x0 >>> 32
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps [.x0, .x7, .x15] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, Instructions.mov, Instructions.shr, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 32 < 64 from by decide, show 0 < 4096 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

def changed : List Reg := [.x0, .x7, .x15] ++ Divide.changed

theorem code_ok (s : State) (lo : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x0 >>> 32).toNat % (s.gpr .x1).toNat ∧
      t.gpr .x7 = s.gpr .x0 ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .x1 (by decide)
  refine (Divide.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .x0) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.2.mono ?_)⟩
    · rw [ht.2.1, ha.high, si]
    · exact (ht.2.2.regs .x7 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr
    · intro r hr; exact List.mem_append_right _ hr

theorem highArgs_secret_rel : RelCT isa (fun s t => s.sp = t.sp) (.block highArgs)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  highArgs_secret_rel.seq Divide.code_secret_rel

end VG.Proof.Argon2.AArch64.ReferenceLane
end

/-! Merged from `Proof.Argon2.AArch64.FirstLane`. -/
section
/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.AArch64.FirstLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FirstLane
open VG.Impl.Argon2.AArch64

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.gpr .x15 = s.gpr .x5 ||| s.gpr .x22 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [test, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.logic, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    BitVec.setWidth_eq, show 0 < 4096 from by decide, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .x4 = s.gpr .x24 ∧ Divide.Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [current, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, ite_true, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x4 = (if s.gpr .x5 = 0 ∧ s.gpr .x22 = 0 then s.gpr .x24 else s.gpr .x4) ∧
    Divide.Keeps [.x8, .x4, .x15] s t := by
  unfold code
  refine WP.seq ((test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .x5 = 0 ∧ s.gpr .x22 = 0))
    (by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact BitVec.or_eq_zero_iff) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .x24 (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .x4 (by decide)

end VG.Proof.Argon2.AArch64.FirstLane
end

/-! Choose the reference lane, restore the pass and prepare the window inputs. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Chosen (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x4 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  pass : t.gpr .x5 = BitVec.ofNat 64 pass
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem chooseLane_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa chooseLane s (Chosen p pass lane slice index s) := by
  have lanesNat : (s.gpr .x1).toNat = p.lanes := by
    rw [ready.lanes, word_nat _ (by have := ready.bounds.lanesBound; omega)]
  unfold chooseLane
  refine WP.seq ((ReferenceLane.code_ok s
    (by rw [lanesNat]; exact ready.bounds.lanesPositive)
    (by rw [lanesNat]; exact ready.bounds.lanesBound)).mono ?_)
  rintro a ⟨laneNat, original, ka⟩
  have ka' : Divide.Keeps changed s a := ka.mono (by decide)
  have readA : InRegions (a.rd ++ a.wr) (a.gpr .x19) 8 := by
    rw [ka'.rd, ka'.wr, ka'.regs .x19 (by decide)]
    exact ready.passRead
  have laneWord : a.gpr .x4 = BitVec.ofNat 64 ((s.gpr .x0 >>> 32).toNat % p.lanes) := by
    calc
      a.gpr .x4 = BitVec.ofNat 64 (a.gpr .x4).toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [laneNat, lanesNat]
  refine WP.seq ((loadPass_ok a readA).mono ?_)
  rintro b ⟨loaded, kb⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kab := ka'.trans kb'
  have pb := ready.position.of_keeps kab
  have passWord : b.gpr .x5 = BitVec.ofNat 64 pass := by
    rw [loaded, ka'.mem, ka'.regs .x19 (by decide)]
    exact ready.passWord
  have passZero : b.gpr .x5 = 0 ↔ pass = 0 := by
    rw [passWord]
    exact word_zero _ (by have := ready.bounds.passBound; omega)
  have sliceZero : b.gpr .x22 = 0 ↔ slice = 0 := by
    rw [pb.slice]
    exact word_zero _ (by have := ready.bounds.sliceBound; omega)
  refine (FirstLane.code_ok b).mono ?_
  rintro t ⟨out, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ready.position.of_keeps (kab.trans kt'), kab.trans kt'⟩
  · rw [out]
    by_cases position : pass = 0 ∧ slice = 0 <;>
      simp only [passZero, sliceZero, pb.current, kb.regs .x4 (by decide), laneWord,
        chosenLane, position, and_self, ite_true, ite_false]
  · exact (kt.regs .x5 (by decide)).trans passWord
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans original)

structure Prepared (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x0 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  current : t.gpr .x1 = BitVec.ofNat 64 lane
  pass : (t.gpr .x5).toNat = pass
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem prepareLanes_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa prepareLanes s (Prepared p pass lane slice index s) := by
  unfold prepareLanes
  refine WP.seq ((chooseLane_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine (laneArgs_ok a).mono ?_
  rintro t ⟨laneOut, currentOut, kt⟩
  have kt' : Divide.Keeps changed a t := kt.mono (by decide)
  refine ⟨laneOut.trans ha.selected, currentOut.trans ha.position.current, ?_,
    (kt.regs .x7 (by decide)).trans ha.original,
    ha.position.of_keeps kt', ha.keeps.trans kt'⟩
  rw [kt.regs .x5 (by decide), ha.pass, word_nat _ (by have := ready.bounds.passBound; omega)]

end VG.Proof.Argon2.AArch64.ReferenceMap

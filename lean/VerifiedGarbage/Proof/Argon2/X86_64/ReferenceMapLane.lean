import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapState
import VerifiedGarbage.Impl.Argon2.X86_64.FirstLane
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceLane
import VerifiedGarbage.Proof.Argon2.X86_64.Divide
import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT

/-! Merged from `Proof.Argon2.X86_64.ReferenceLane`. -/
section
/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.X86_64.ReferenceLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceLane

structure Prefix (s t : State) : Prop where
  high : t.gpr .rdi = s.gpr .rdi >>> 32
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps [.rdi, .r11] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, RegUpd.gpr_setReg,
    show 1 ≤ (32 : Nat) ∧ (32 : Nat) ≤ 63 from by decide,
    and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  all_goals rfl

def changed : List Reg := [.rdi, .r11] ++ Divide.changed

theorem code_ok (s : State) (lo : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .r8).toNat = (s.gpr .rdi >>> 32).toNat % (s.gpr .rsi).toNat ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .rsi (by decide)
  refine (Divide.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .rdi) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.2.mono ?_)⟩
    · rw [ht.2.1, ha.high, si]
    · exact (ht.2.2.regs .r11 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr
    · intro r hr; exact List.mem_append_right _ hr

theorem highArgs_secret_rel : RelCT isa (fun _ _ => True) (.block highArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  highArgs_secret_rel.seq Divide.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceLane
end

/-! Merged from `Proof.Argon2.X86_64.FirstLane`. -/
section
/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.X86_64.FirstLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FirstLane

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.zf = decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0) ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [test, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change (s.gpr .r9 ||| s.gpr .r14) = 0#64 ↔ _
    exact BitVec.or_eq_zero_iff
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .r8 = s.gpr .rbx ∧ Divide.Keeps [.r8] s t := by
  apply WP.of_runBlock
  simp only [current, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r8 = (if s.gpr .r9 = 0 ∧ s.gpr .r14 = 0 then s.gpr .rbx else s.gpr .r8) ∧
    Divide.Keeps [.rax, .r8] s t := by
  unfold code
  refine WP.seq ((test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0))
    (by simp only [eval, flag]) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .rbx (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .r8 (by decide)

end VG.Proof.Argon2.X86_64.FirstLane
end

/-! Choose the reference lane, restore the pass and prepare the window inputs. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Chosen (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r8 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  pass : t.gpr .r9 = BitVec.ofNat 64 pass
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem chooseLane_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa chooseLane s (Chosen p pass lane slice index s) := by
  have lanesNat : (s.gpr .rsi).toNat = p.lanes := by
    rw [ready.lanes, word_nat _ (by have := ready.bounds.lanesBound; omega)]
  unfold chooseLane
  refine WP.seq ((ReferenceLane.code_ok s
    (by rw [lanesNat]; exact ready.bounds.lanesPositive)
    (by rw [lanesNat]; exact ready.bounds.lanesBound)).mono ?_)
  rintro a ⟨laneNat, original, ka⟩
  have ka' : Divide.Keeps changed s a := ka.mono (by decide)
  have readA : InRegions (a.rd ++ a.wr) (a.gpr .rbp) 8 := by
    rw [ka'.rd, ka'.wr, ka'.regs .rbp (by decide)]
    exact ready.passRead
  have laneWord : a.gpr .r8 = BitVec.ofNat 64 ((s.gpr .rdi >>> 32).toNat % p.lanes) := by
    calc
      a.gpr .r8 = BitVec.ofNat 64 (a.gpr .r8).toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [laneNat, lanesNat]
  refine WP.seq ((loadPass_ok a readA).mono ?_)
  rintro b ⟨loaded, kb⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kab := ka'.trans kb'
  have pb := ready.position.of_keeps kab
  have passWord : b.gpr .r9 = BitVec.ofNat 64 pass := by
    rw [loaded, ka'.mem, ka'.regs .rbp (by decide)]
    exact ready.passWord
  have passZero : b.gpr .r9 = 0 ↔ pass = 0 := by
    rw [passWord]
    exact word_zero _ (by have := ready.bounds.passBound; omega)
  have sliceZero : b.gpr .r14 = 0 ↔ slice = 0 := by
    rw [pb.slice]
    exact word_zero _ (by have := ready.bounds.sliceBound; omega)
  refine (FirstLane.code_ok b).mono ?_
  rintro t ⟨out, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ready.position.of_keeps (kab.trans kt'), kab.trans kt'⟩
  · rw [out]
    by_cases position : pass = 0 ∧ slice = 0 <;>
      simp only [passZero, sliceZero, pb.current, kb.regs .r8 (by decide), laneWord,
        chosenLane, position, and_self, ite_true, ite_false]
  · exact (kt.regs .r9 (by decide)).trans passWord
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans original)

structure Prepared (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .rdi = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  current : t.gpr .rsi = BitVec.ofNat 64 lane
  pass : (t.gpr .r9).toNat = pass
  original : t.gpr .r11 = s.gpr .rdi
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
    (kt.regs .r11 (by decide)).trans ha.original,
    ha.position.of_keeps kt', ha.keeps.trans kt'⟩
  rw [kt.regs .r9 (by decide), ha.pass, word_nat _ (by have := ready.bounds.passBound; omega)]

end VG.Proof.Argon2.X86_64.ReferenceMap

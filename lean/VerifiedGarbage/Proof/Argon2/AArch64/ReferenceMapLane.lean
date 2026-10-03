import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceLane
import VerifiedGarbage.Proof.Argon2.AArch64.FirstLane

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

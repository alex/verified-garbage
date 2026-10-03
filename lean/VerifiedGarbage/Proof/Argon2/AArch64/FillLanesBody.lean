import VerifiedGarbage.Proof.Argon2.AArch64.FillLaneAdvance

/-! One lane iteration fills its segment and advances the public lane. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 (lane + 1)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x23 → t.gpr r = s.gpr r
  header : ∃ a, SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.x24, .x12, .x13, .x14, .x15] a t
  cf : eval (.nonzero .x .x14) t = some (decide (lane + 1 < p.lanes))
  next : lane + 1 < p.lanes → SegmentSetup.Ready p pass (lane + 1) slice t

theorem body_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillLanes.body s (Done s · p pass lane slice state) := by
  unfold Impl.Argon2.AArch64.FillLanes.body
  refine WP.seq ((SegmentSetup.code_ok s p pass lane slice h state represented).mono ?_)
  intro a filled
  have ready := finished_ready h.parameters filled
  obtain ⟨old, words⟩ := ready.words
  have added : a.gpr .x24 + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [words.laneWord, BitVec.ofNat_add]; rfl
  have laneBound := h.parameters.laneBound
  have lanesBound32 := h.parameters.lanesBound
  have left : (a.gpr .x24 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (lane + 1) (by omega)]; omega
  have right : (a.mem.readW (off (a.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [ready.lanesWord, ReferenceMap.word_nat p.lanes (by omega)]; omega
  refine (advance_ok a (ready.layout.frameRead 184 (by simp)) left right).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have nextWord := value.trans added
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans h.parameters.lanesBound (by decide)
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextWord, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ⟨a, ready, keeps⟩, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx ix
    have outside : r ∉ [Reg.x24, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr ix)
  · rw [flag, added, ready.lanesWord, ReferenceMap.word_nat (lane + 1) (by omega),
      ReferenceMap.word_nat p.lanes lanesBound]
  · intro active; exact change_lane_ready ready keeps nextWord active

end VG.Proof.Argon2.AArch64.FillLanes

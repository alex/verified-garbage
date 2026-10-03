import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.AArch64.FillSegment
import VerifiedGarbage.Proof.Argon2.SegmentIndices
import VerifiedGarbage.Proof.Argon2.AArch64.FillSegmentBody
import VerifiedGarbage.Proof.Argon2.AArch64.FillBlock
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompress
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressOperation
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.FillPointersLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Proof.Argon2.AArch64.RandomSourcePrepare
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheSelect
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheWord
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCalls
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderLit
import VerifiedGarbage.Impl.Argon2.AArch64.AddressMode
import VerifiedGarbage.Proof.Argon2.AArch64.DependentWord
import VerifiedGarbage.Impl.Argon2.AArch64.DependentWord
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
import VerifiedGarbage.Proof.Argon2.AArch64.RandomSource
import VerifiedGarbage.Proof.Argon2.AArch64.Relative
import VerifiedGarbage.Proof.Argon2.AArch64.Wrap
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapLane
import VerifiedGarbage.Impl.Argon2.AArch64.FirstLane
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare

/-! Merged from `Proof.Argon2.AArch64.SegmentSetupTrace`. -/
section
/-! Cache reset and initial-index selection branch only on public parameters. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure RelatedReady (p : Params) (pass lane slice : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice s
  right : Ready p pass lane slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem RelatedReady.of_keeps {p : Params} {pass lane slice : Nat} {s t a b : State}
    (h : RelatedReady p pass lane slice s t)
    (ka : Divide.Keeps [.x8, .x3, .x23, .x13, .x14, .x15] s a) (kb : Divide.Keeps [.x8, .x3, .x23, .x13, .x14, .x15] t b) :
    RelatedReady p pass lane slice a b := by
  have protectedRegs : ∀ r ∈ [Reg.x19, .x24, .x20, .x21, .x22], r ∉ [Reg.x8, .x3, .x23, .x13, .x14, .x15] := by decide
  refine ⟨h.left.of_state (fun r hr => ka.regs r (protectedRegs r hr)) ka.sp ka.mem ka.rd ka.wr,
    h.right.of_state (fun r hr => kb.regs r (protectedRegs r hr)) kb.sp kb.mem kb.rd kb.wr, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.work

theorem reset_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    reset (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem reset_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) reset (RelatedReady p pass lane slice) := by
  have trace := reset_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨reset_ok s p pass lane slice h.left, reset_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.ready, hb.ready, ?_, ?_, ha.matrix.trans (hp.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩
  · rw [ha.regs .x19 (by simp [FillCompress.loopRegs]), hb.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.bases
  · rw [ha.sp, hb.sp]; exact hp.stacks

theorem first_spec_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa (.block first) s fun t => eval (.zero .x .x15) t = some (decide (pass = 0 ∧ slice = 0)) ∧ Divide.Keeps [.x3, .x13, .x14, .x15] s t := by
  obtain ⟨old, words⟩ := h.words
  refine (first_ok s (h.reads 0 (by simp))).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨?_, keeps⟩
  rw [flag, words.passWord, words.sliceWord]
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 :=
    ReferenceMap.word_zero pass (Nat.lt_trans h.parameters.passBound (by decide))
  have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 :=
    ReferenceMap.word_zero slice (Nat.lt_trans h.parameters.sliceBound (by decide))
  simp only [passZero, sliceZero]

theorem first_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block first) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem first_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) (.block first)
      (fun s t => RelatedReady p pass lane slice s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t) := by
  have trace := first_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨first_spec_ok s p pass lane slice h.left, first_spec_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps (ka.mono (by decide)) (kb.mono (by decide)), fa.trans fb.symm⟩

theorem index_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) index (fun _ _ => True) := by
  have two : RelCT isa (fun s t : State => s.sp = t.sp)
      (.block [Impl.Argon2.AArch64.Instructions.imm .x23 2].flatten) (fun _ _ => True) :=
    (RelCT.taintRegs (τ := Taint.ofRegs [])
      (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
      [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have zero : RelCT isa (fun s t : State => s.sp = t.sp)
      (.block [Impl.Argon2.AArch64.Instructions.imm .x23 0].flatten) (fun _ _ => True) :=
    (RelCT.taintRegs (τ := Taint.ofRegs [])
      (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
      [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have branches : RelCT isa (fun s t => RelatedReady p pass lane slice s t ∧
      eval (.zero .x .x15) s = eval (.zero .x .x15) t)
      (.ite (.zero .x .x15)
        (.block [Impl.Argon2.AArch64.Instructions.imm .x23 2].flatten)
        (.block [Impl.Argon2.AArch64.Instructions.imm .x23 0].flatten)) (fun _ _ => True) :=
    RelCT.ite (by intro s t h; exact h.2)
      (two.mono (fun _ _ h => h.1.1.stacks) (fun _ _ h => h))
      (zero.mono (fun _ _ h => h.1.1.stacks) (fun _ _ h => h))
  exact (first_public_rel p pass lane slice).seq branches

theorem prepare_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) prepare (fun _ _ => True) :=
  (reset_public_rel p pass lane slice).seq (index_trace p pass lane slice)

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceStartLit`. -/
section
/-! A checked literal for the chronological reference-window start. -/

namespace VG

materialize_code Impl.Argon2.AArch64.ReferenceStart.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceStartCT`. -/
section
/-! Branches depend only on the public position. -/
namespace VG.Proof.Argon2.AArch64.ReferenceStart
open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceStart

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x5, .x22, .x21], s.gpr r = t.gpr r) code
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x6], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x22, .x21])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [.x6] (by taint_decide)
end VG.Proof.Argon2.AArch64.ReferenceStart
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapWindowCT`. -/
section
/-! The chronological window branches only on the public pass and slice. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

def PublicPosition (s t : State) : Prop :=
  s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x22, .x21], s.gpr r = t.gpr r

theorem window_rel : RelCT isa PublicPosition window (fun s t => s.sp = t.sp) := by
  have start := ReferenceStart.code_rel.wpDep (fun s t _ =>
    ⟨ReferenceStart.code_ok s, ReferenceStart.code_ok t⟩)
  refine start.seq (ReferenceCount.code_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨eq.1, (ha.2.regs .x5 (by decide)).trans
    ((hp.2 .x5 (by simp)).trans (hb.2.regs .x5 (by decide)).symm)⟩

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapLaneCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FirstLaneLit`. -/
section
/-! A checked literal for the public first-slice lane override. -/

namespace VG

materialize_code Impl.Argon2.AArch64.FirstLane.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.FirstLaneCT`. -/
section
/-! Branches depend only on the public position. -/
namespace VG.Proof.Argon2.AArch64.FirstLane
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FirstLane

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x5, .x22], s.gpr r = t.gpr r) code
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x22])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)
end VG.Proof.Argon2.AArch64.FirstLane
end

/-! Recover the public pass from the frame without exposing the secret word. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

def Related (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  Ready p pass lane slice index s ∧ Ready p pass lane slice index t ∧ s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp

theorem division_keeps (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceLane.code s fun t =>
      Ready p pass lane slice index t ∧ Divide.Keeps changed s t := by
  refine (ReferenceLane.code_ok s
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesPositive)
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesBound)).mono ?_
  rintro t ⟨_, _, keeps⟩
  have k : Divide.Keeps changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .x1 (by decide)), k⟩

theorem division_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index)
      VG.Impl.Argon2.AArch64.ReferenceLane.code (Related p pass lane slice index) := by
  have full := (ReferenceLane.code_secret_rel.mono
    (P' := Related p pass lane slice index) (fun _ _ hp => hp.2.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨division_keeps s p pass lane slice index hp.1,
        division_keeps t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .x19 (by decide)).trans
    (hp.2.2.1.trans (hb.2.regs .x19 (by decide)).symm), eq⟩

theorem loadPass_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block loadPass) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

def Loaded (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  Related p pass lane slice index s t ∧
    s.gpr .x5 = BitVec.ofNat 64 pass ∧ t.gpr .x5 = BitVec.ofNat 64 pass

theorem loadPass_public (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) : WP isa (.block loadPass) s fun t =>
      Ready p pass lane slice index t ∧ t.gpr .x5 = BitVec.ofNat 64 pass ∧
        Divide.Keeps changed s t := by
  refine (loadPass_ok s ready.passRead).mono ?_
  rintro t ⟨loaded, keeps⟩
  have k : Divide.Keeps changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .x1 (by decide)), loaded.trans ready.passWord, k⟩

theorem loadPass_public_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) (.block loadPass)
      (Loaded p pass lane slice index) := by
  have full := (loadPass_rel.mono (P' := Related p pass lane slice index)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨loadPass_public s p pass lane slice index hp.1,
        loadPass_public t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨⟨ha.1, hb.1, (ha.2.2.regs .x19 (by decide)).trans
    (hp.2.2.1.trans (hb.2.2.regs .x19 (by decide)).symm), eq⟩, ha.2.1, hb.2.1⟩

theorem firstLane_loaded_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Loaded p pass lane slice index) VG.Impl.Argon2.AArch64.FirstLane.code
      (Loaded p pass lane slice index) := by
  have trace := FirstLane.code_rel.mono (P' := Loaded p pass lane slice index)
    (fun _ _ hp => ⟨hp.1.2.2.2, by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.2.1.trans hp.2.2.symm
      · exact hp.1.1.position.slice.trans hp.1.2.1.position.slice.symm⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t _ => ⟨FirstLane.code_ok s, FirstLane.code_ok t⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  have ka : Divide.Keeps changed s a := ha.2.mono (by decide)
  have kb : Divide.Keeps changed t b := hb.2.mono (by decide)
  refine ⟨⟨hp.1.1.of_keeps ka (ha.2.regs .x1 (by decide)),
    hp.1.2.1.of_keeps kb (hb.2.regs .x1 (by decide)),
    (ka.regs .x19 (by decide)).trans (hp.1.2.2.1.trans (kb.regs .x19 (by decide)).symm), eq.1⟩, ?_, ?_⟩
  · exact (ha.2.regs .x5 (by decide)).trans hp.2.1
  · exact (hb.2.regs .x5 (by decide)).trans hp.2.2

theorem laneArgs_secret_rel : RelCT isa (fun s t => s.sp = t.sp) (.block laneArgs)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepareLanes_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) prepareLanes PublicPosition := by
  have head := (division_rel p pass lane slice index).seq
    ((loadPass_public_rel p pass lane slice index).seq (firstLane_loaded_rel p pass lane slice index))
  have trace := head.seq (laneArgs_secret_rel.mono (fun _ _ hp => hp.1.2.2.2) (fun _ _ h => h))
  have full := trace.wpDep (fun s t hp =>
    ⟨prepareLanes_ok s p pass lane slice index hp.1,
      prepareLanes_ok t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, _, _, _, ha, hb⟩ := h
  refine ⟨eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    exact ha.pass.trans hb.pass.symm
  · exact ha.position.slice.trans hb.position.slice.symm
  · exact ha.position.segmentLength.trans hb.position.segmentLength.symm

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapCT`. -/
section
/-! Complete reference mapping has no secret-dependent execution trace. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem relativeArgs_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.block relativeArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem wrapArgs_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.block wrapArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem tail_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.seq relative finish) (fun s t => s.sp = t.sp) :=
  (relativeArgs_secret_rel.seq Relative.code_secret_rel).seq
    (wrapArgs_secret_rel.seq Wrap.code_secret_rel)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun s t => s.sp = t.sp) :=
  (prepareLanes_rel p pass lane slice index).seq (window_rel.seq tail_secret_rel)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.RandomSourceCounter`. -/
section
/-! The stored address counter remains public after either source. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

def counterValue (p : Params) (pass slice index old : Nat) : Addr :=
  BitVec.ofNat 64 (if independent p pass slice then index / 128 + 1 else old)

theorem counter_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) :
    WP isa Impl.Argon2.AArch64.RandomSource.code s fun t =>
      t.mem.readW (off (t.gpr .x19) 8) 64 = counterValue p pass slice index old := by
  unfold Impl.Argon2.AArch64.RandomSource.code
  refine WP.seq ((prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  refine WP.ite (!independent p pass slice) flag ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by cases eq : independent p pass slice <;> simp_all
    refine (DependentWord.code_ok a p pass lane slice index next.filling).mono ?_
    rintro t ⟨_, saved⟩
    unfold counterValue
    simp only [dependent]
    rw [saved.mem, saved.regs .x19 (by decide)]
    exact next.cache.words.counterWord
  · intro mode
    have independent : independent p pass slice = true := by cases eq : independent p pass slice <;> simp_all
    refine (AddressCache.code_ok p pass lane slice old a next.cache.ready).mono ?_
    intro t done
    unfold counterValue
    simp only [independent, ite_true]
    rw [done.selected.counterWord, AddressCache.counter_nat, next.index_nat]

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillCompressCallCT`. -/
section
/-! Compression calls reveal only their argument addresses and stack pointer. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64

theorem call_rel (name : String) {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
      s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.sp = t.sp) :
    RelCT isa P (.call name Impl.Argon2.AArch64.compress) (fun _ _ => True) := by
  apply RelCT.callEx (k := compressLocal) compress_correct compress_ct
  intro s t hp
  obtain ⟨hs, ht, di, si, dx, cx, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := call_hyps s hs
  obtain ⟨pt, ct, wt⟩ := call_hyps t ht
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧ s.sp = t.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs)]
  exact ⟨di, si, dx, cx, sp⟩

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Merged from `Proof.Argon2.AArch64.RandomSourceCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DependentWordLit`. -/
section
namespace VG.Impl.Argon2.AArch64.DependentWord
materialize_code pointer
end VG.Impl.Argon2.AArch64.DependentWord
end

/-! Merged from `Proof.Argon2.AArch64.DependentWordCT`. -/
section
/-! The previous cell is read at an address determined by public parameters. -/
namespace VG.Proof.Argon2.AArch64.DependentWord
open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : FillKernel.Ready p pass lane slice index s
  right : FillKernel.Ready p pass lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t

theorem pointer_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    pointer (fun s t => s.sp = t.sp) := by
  have trace := RelCT.taintRegs (c := pointer) (τ := Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
    (P := fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)
  exact trace.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem read_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8)
    (.block Impl.Argon2.AArch64.DependentWord.read) (fun s t => s.sp = t.sp) := by
  have trace := RelCT.taintRegs (c := .block Impl.Argon2.AArch64.DependentWord.read)
    (τ := Taint.ofRegs [.x8]) (P := fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8)
    (fun _ _ h => ⟨h.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r; exact h.2⟩) [] (by taint_decide)
  exact trace.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun s t => s.sp = t.sp) := by
  have trace := pointer_rel.mono (P' := Related p pass lane slice index) (by
    intro s t h
    refine ⟨h.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.bases
    · exact h.left.position.laneLength.trans h.right.position.laneLength.symm
    · exact h.left.position.segmentLength.trans h.right.position.segmentLength.symm
    · exact h.left.position.slice.trans h.right.position.slice.symm
    · exact h.left.position.index.trans h.right.position.index.symm) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨pointer_ok s p pass lane slice index h.left, pointer_ok t p pass lane slice index h.right⟩)
  have publicTrace : RelCT isa (Related p pass lane slice index) pointer
      (fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨sp, s, t, hp, ⟨pa, _⟩, ⟨pb, _⟩⟩ := h
    have equal : FillKernel.previous s p lane slice index = FillKernel.previous t p lane slice index := by
      unfold FillKernel.previous; rw [hp.matrices]
    exact ⟨sp, pa.trans (equal.trans pb.symm)⟩)
  exact publicTrace.seq read_rel

end VG.Proof.Argon2.AArch64.DependentWord
end

/-! Merged from `Proof.Argon2.AArch64.AddressModeLit`. -/
section
/-! Checked literal of the segment addressing-mode computation. -/

namespace VG

materialize_code Impl.Argon2.AArch64.AddressMode.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.AddressModeCT`. -/
section
/-! Mode selection has a fixed trace at the public frame base. -/
namespace VG.Proof.Argon2.AArch64.AddressMode
open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressMode

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.AddressMode
end

/-! Merged from `Proof.Argon2.AArch64.AddressInputCT`. -/
section
/-! Clearing and header preparation visit fixed offsets of public pointers. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64

theorem ClearBlock.code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0)
    Impl.Argon2.AArch64.ClearBlock.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.2⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem AddressHeader.code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x19], s.gpr r = t.gpr r)
    Impl.Argon2.AArch64.AddressHeader.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x19])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64
end

/-! Merged from `Proof.Argon2.AArch64.AddressGenerationCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.AddressCallsCT`. -/
section
/-! The two address-generation compression calls have public fixed addresses. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  work : work s = work t

structure CallRelated (s t : State) : Prop where
  left : FillCompress.CallReady s
  right : FillCompress.CallReady t
  stacks : s.sp = t.sp
  args : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], s.gpr r = t.gpr r

theorem first_args_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (args 7168 5120 4096)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem second_args_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (args 7168 4096 6144)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem args_public_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (args x y out)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (.block (args x y out)) CallRelated := by
  have trace := argTrace.mono (P' := Related) (fun _ _ hp => ⟨hp.bases, hp.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨args_nat_ok s hp.left x y out (by omega) (by omega) (by omega),
      args_nat_ok t hp.right x y out (by omega) (by omega) (by omega)⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨args_call_ready s a hp.left x y out hx hy ho bx by_ bo ha,
    args_call_ready t b hp.right x y out hx hy ho bx by_ bo hb, eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha.left.trans ((congrArg (fun p => off p x) hp.work).trans hb.left.symm)
  · exact ha.right.trans ((congrArg (fun p => off p y) hp.work).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (fun p => off p out) hp.work).trans hb.output.symm)
  · exact ha.scratch.trans (hp.work.trans hb.scratch.symm)

theorem stage_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (args x y out)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (stage x y out) Related := by
  have call := FillCompress.call_rel Spec.Argon2.compressApi.name (P := CallRelated)
    (fun _ _ hp => ⟨hp.left, hp.right, hp.args .x0 (by simp), hp.args .x1 (by simp),
      hp.args .x2 (by simp), hp.args .x3 (by simp), hp.stacks⟩)
  have trace := (args_public_rel x y out hx hy ho bx by_ bo argTrace).seq call
  have full := trace.wpDep (fun s t hp =>
    ⟨stage_ok s hp.left x y out hx hy ho bx by_ bo,
      stage_ok t hp.right x y out hx hy ho bx by_ bo⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready, hb.ready,
    (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm),
    ha.sp.trans (hp.stacks.trans hb.sp.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩

theorem calls_rel : RelCT isa Related calls Related :=
  (stage_rel 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) first_args_rel).seq
  (stage_rel 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) second_args_rel)

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Independent-address generation keeps its entire trace independent of secrets. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls

theorem Related.of_stable {s t a b : State} (h : Related s t)
    (ha : Stable s a) (hb : Stable t b) : Related a b :=
  ⟨ha.ready, hb.ready,
    (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (h.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm),
    ha.sp.trans (h.stacks.trans hb.sp.symm),
    ha.work_eq.trans (h.work.trans hb.work_eq.symm)⟩

theorem input_pointer_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (pointer 5120)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem zero_pointer_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (pointer 7168)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

structure PointRelated (s t : State) : Prop where
  related : Related s t
  pointer : s.gpr .x0 = t.gpr .x0

theorem pointer_public_rel (offset : Nat) (bound : offset ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (pointer offset)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (.block (pointer offset)) PointRelated := by
  have publicTrace := trace.mono (P' := Related) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := publicTrace.wpDep (fun s t h =>
    ⟨pointer_ok s offset bound h.left.frameRead, pointer_ok t offset bound h.right.frameRead⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨pa, ka⟩, ⟨pb, kb⟩⟩ := h
  exact ⟨hp.of_stable (pointer_stable hp.left ka) (pointer_stable hp.right kb),
    pa.trans ((congrArg (· + BitVec.ofNat 64 offset) hp.work).trans pb.symm)⟩

theorem clearAt_rel (offset : Nat) (bound : offset + 1024 ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (pointer offset)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (clearAt offset) Related := by
  have clear := ClearBlock.code_rel.mono (P' := PointRelated)
    (fun _ _ h => ⟨h.related.stacks, h.pointer⟩) (fun _ _ h => h)
  have blocks := (pointer_public_rel offset (by omega) trace).seq clear
  have full := blocks.wpDep (fun s t h =>
    ⟨clearAt_ok s h.left offset bound, clearAt_ok t h.right offset bound⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.of_stable (ha.stable bound) (hb.stable bound)

structure PrepareRelated (s t : State) : Prop where
  related : Related s t
  leftReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  rightReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8

theorem prepare_rel : RelCT isa PrepareRelated prepare Related := by
  have header := AddressHeader.code_rel.mono (P' := PointRelated) (by
    intro s t h
    refine ⟨h.related.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.pointer
    · exact h.related.bases) (fun _ _ h => h)
  have trace := (clearAt_rel 5120 (by decide) input_pointer_rel).seq
    ((clearAt_rel 7168 (by decide) zero_pointer_rel).seq
      ((pointer_public_rel 5120 (by decide) input_pointer_rel).seq header))
  have narrowed := trace.mono (P' := PrepareRelated) (fun _ _ h => h.related) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨prepare_layout_ok s h.related.left h.leftReads,
      prepare_layout_ok t h.related.right h.rightReads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.related.of_stable ha.stable hb.stable

theorem code_rel : RelCT isa PrepareRelated code Related := prepare_rel.seq calls_rel

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheWordCT`. -/
section
/-! The cached random word is secret; its read address is public. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache

structure WordRelated (s t : State) : Prop where
  layout : AddressCalls.Related s t
  indices : s.gpr .x23 = t.gpr .x23

theorem wordArgs_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x23], s.gpr r = t.gpr r)
    (.block wordArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem wordRead_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x3, .x8], s.gpr r = t.gpr r)
    (.block wordRead) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x3, .x8])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem word_rel : RelCT isa WordRelated Impl.Argon2.AArch64.AddressCache.word (fun s t => s.sp = t.sp) := by
  have trace := wordArgs_rel.mono (P' := WordRelated) (by
    intro s t h
    refine ⟨h.layout.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.layout.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨wordArgs_ok s h.layout.left.frameRead, wordArgs_ok t h.layout.right.frameRead⟩)
  have args : RelCT isa WordRelated (.block wordArgs)
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x3, .x8], s.gpr r = t.gpr r) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨eq, s, t, hp, ⟨sa, ia, _⟩, ⟨sb, ib, _⟩⟩ := h
    refine ⟨eq, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sa.trans (hp.layout.work.trans sb.symm)
    · exact ia.trans ((congrArg (· &&& 127) hp.indices).trans ib.symm))
  exact args.seq wordRead_rel

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheSelectCT`. -/
section
/-! Cache regeneration branches only on public counters. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache

structure CacheRelated (s t : State) : Prop where
  prepare : AddressCalls.PrepareRelated s t
  indices : s.gpr .x23 = t.gpr .x23
  counters : s.mem.readW (off (s.gpr .x19) 8) 64 = t.mem.readW (off (t.gpr .x19) 8) 64
  leftWrite : InRegions s.wr (off (s.gpr .x19) 8) 8
  rightWrite : InRegions t.wr (off (t.gpr .x19) 8) 8

structure CheckedRelated (s t : State) : Prop where
  related : CacheRelated s t
  values : s.gpr .x8 = t.gpr .x8
  flags : s.gpr .x15 = t.gpr .x15

theorem check_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x23], s.gpr r = t.gpr r)
    (.block check) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem check_public_rel : RelCT isa CacheRelated (.block check) CheckedRelated := by
  have trace := check_rel.mono (P' := CacheRelated) (by
    intro s t h
    refine ⟨h.prepare.related.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.prepare.related.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨check_ok s (h.prepare.leftReads 8 (by simp)), check_ok t (h.prepare.rightReads 8 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨va, fa, ka⟩, ⟨vb, fb, kb⟩⟩ := h
  have sa := check_stable hp.prepare.related.left ka
  have sb := check_stable hp.prepare.related.right kb
  have index : a.gpr .x23 = b.gpr .x23 := (sa.regs .x23 (by simp [FillCompress.loopRegs])).trans
    (hp.indices.trans (sb.regs .x23 (by simp [FillCompress.loopRegs])).symm)
  have counters : a.mem.readW (off (a.gpr .x19) 8) 64 = b.mem.readW (off (b.gpr .x19) 8) 64 := by
    rw [ka.mem, kb.mem, sa.regs .x19 (by simp [FillCompress.loopRegs]), sb.regs .x19 (by simp [FillCompress.loopRegs])]
    exact hp.counters
  refine ⟨⟨⟨hp.prepare.related.of_stable sa sb, sa.reads hp.prepare.leftReads,
    sb.reads hp.prepare.rightReads⟩, index, counters, ?_, ?_⟩, ?_, ?_⟩
  · rw [ka.wr, sa.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.leftWrite
  · rw [kb.wr, sb.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.rightWrite
  · rw [va, vb, hp.indices]
  · rw [fa, fb, hp.indices, hp.counters]

theorem save_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block save) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem save_public_rel : RelCT isa CheckedRelated (.block save) AddressCalls.PrepareRelated := by
  have trace := save_rel.mono (P' := CheckedRelated)
    (fun _ _ h => ⟨h.related.prepare.related.bases, h.related.prepare.related.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨save_ready s h.related.prepare.related.left h.related.leftWrite,
      save_ready t h.related.prepare.related.right h.related.rightWrite⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ha.work_eq.trans
    (hp.related.prepare.related.work.trans hb.work_eq.symm)⟩, ?_, ?_⟩
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.bases
  · exact ha.sp.trans (hp.related.prepare.related.stacks.trans hb.sp.symm)
  · rw [ha.rd, ha.wr, ha.regs]; exact hp.related.prepare.leftReads
  · rw [hb.rd, hb.wr, hb.regs]; exact hp.related.prepare.rightReads

theorem select_trace : RelCT isa CacheRelated select (fun _ _ => True) := by
  have noop : RelCT isa (fun s t : State => s.sp = t.sp) (.block []) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) (by taint_decide)
  have branches : RelCT isa CheckedRelated
      (.ite (.zero .x .x15) (.block []) (.seq (.block save) Impl.Argon2.AArch64.AddressCalls.code))
      (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, State.read, h.flags])
      (noop.mono (fun _ _ h => h.1.related.prepare.related.stacks) (fun _ _ h => h))
      ((save_public_rel.seq AddressCalls.code_rel).mono (fun _ _ h => h.1) (fun _ _ _ => trivial))
  exact check_public_rel.seq branches

structure ReadyRelated (p : Spec.Argon2.Params) (pass lane slice old : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice old s
  right : Ready p pass lane slice old t
  pubs : CacheRelated s t

theorem select_public_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (ReadyRelated p pass lane slice old) select WordRelated := by
  have trace := select_trace.mono (P' := ReadyRelated p pass lane slice old)
    (fun _ _ h => h.pubs) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨selected_ok p pass lane slice old s h.left, selected_ok p pass lane slice old t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.layout, hb.layout, ?_, ?_, ha.work_eq.trans
    (hp.pubs.prepare.related.work.trans hb.work_eq.symm)⟩, ?_⟩
  · exact (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.pubs.prepare.related.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm)
  · exact ha.sp.trans (hp.pubs.prepare.related.stacks.trans hb.sp.symm)
  · exact (ha.regs .x23 (by simp [FillCompress.loopRegs])).trans
      (hp.pubs.indices.trans (hb.regs .x23 (by simp [FillCompress.loopRegs])).symm)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (ReadyRelated p pass lane slice old) code (fun s t => s.sp = t.sp) :=
  (select_public_rel p pass lane slice old).seq word_rel

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Source dispatch and cached-word selection use only public addresses and guards. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.RandomSource

structure Related (p : Params) (pass lane slice index old : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice index old s
  right : Ready p pass lane slice index old t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem Related.of_keeps {p : Params} {pass lane slice index old : Nat} {s t a b : State}
    (h : Related p pass lane slice index old s t)
    (ka : Divide.Keeps ReferenceMap.changed s a) (kb : Divide.Keeps ReferenceMap.changed t b) :
    Related p pass lane slice index old a b := by
  refine ⟨h.left.of_keeps ka, h.right.of_keeps kb, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.work

theorem test_rel : RelCT isa (fun s t : State => s.sp = t.sp) (.block test)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepare_rel (p : Params) (pass lane slice index old : Nat) :
    RelCT isa (Related p pass lane slice index old) prepare
      (fun s t => Related p pass lane slice index old s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t) := by
  have trace := AddressMode.code_rel.seq test_rel
  have narrowed := trace.mono (P' := Related p pass lane slice index old)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨prepare_ok s p pass lane slice index old h.left,
      prepare_ok t p pass lane slice index old h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa.trans fb.symm⟩

theorem Related.cache {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Related p pass lane slice index old s t) : AddressCache.ReadyRelated p pass lane slice old s t := by
  refine ⟨h.left.cache.ready, h.right.cache.ready,
    ⟨⟨⟨h.left.cache.layout, h.right.cache.layout, h.bases, h.stacks, h.work⟩,
      h.left.cache.reads, h.right.cache.reads⟩, ?_, ?_, h.left.cache.write, h.right.cache.write⟩⟩
  · exact h.left.filling.position.index.trans h.right.filling.position.index.symm
  · exact h.left.cache.words.counterWord.trans h.right.cache.words.counterWord.symm

theorem code_rel (p : Params) (pass lane slice index old : Nat) :
    RelCT isa (Related p pass lane slice index old) code (fun s t => s.sp = t.sp) := by
  have branches : RelCT isa
      (fun s t => Related p pass lane slice index old s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t)
      (.ite (.zero .x .x15) Impl.Argon2.AArch64.DependentWord.code Impl.Argon2.AArch64.AddressCache.code)
      (fun s t => s.sp = t.sp) := by
    apply RelCT.ite (by intro s t h; exact h.2)
    · exact (DependentWord.code_rel p pass lane slice index).mono
        (fun _ _ h => ⟨h.1.1.left.filling, h.1.1.right.filling, h.1.1.bases, h.1.1.stacks, h.1.1.matrices⟩)
        (fun _ _ h => h)
    · exact (AddressCache.code_rel p pass lane slice old).mono
        (fun _ _ h => h.1.1.cache) (fun _ _ h => h)
  exact (prepare_rel p pass lane slice index old).seq branches

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillWriteLit`. -/
section
/-! Checked literal of the complete copy/XOR block write. -/

namespace VG

materialize_code Impl.Argon2.AArch64.FillWrite.code

end VG
end

/-! Merged from `Proof.Argon2.AArch64.FillWriteCT`. -/
section
/-! Both write paths have a public, fixed sequence of memory accesses. -/
namespace VG.Proof.Argon2.AArch64.FillWrite
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillWrite

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x0, .x1], s.gpr r = t.gpr r) code
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x0, .x1])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      exact h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Merged from `Proof.Argon2.AArch64.FillSegmentCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSegmentBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillPointersCT`. -/
section
/-! Pointer setup only branches on the public current column. -/
namespace VG.Proof.Argon2.AArch64.FillPointers
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x24, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    code (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x6], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x4, .x24, .x20, .x21, .x22, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [Reg.x6] (by taint_decide)
end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Merged from `Proof.Argon2.AArch64.FillKernelMappingCT`. -/
section
/-! Reference mapping exposes no more than the permitted reference coordinates. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice index s
  right : Ready p pass lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  scratch : work s = work t
  references : Spec.Argon2.reference p pass lane slice index (s.gpr .x0) =
    Spec.Argon2.reference p pass lane slice index (t.gpr .x0)

structure PointerRelated (p : Params) (lane slice index : Nat) (s t : State) : Prop where
  left : Layout p s
  right : Layout p t
  leftPosition : ReferenceMap.Position p lane slice index s
  rightPosition : ReferenceMap.Position p lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  matrices : matrix s = matrix t
  stacks : s.sp = t.sp

theorem lanes_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FillKernel.lanes) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem lanes_ready (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa (.block Impl.Argon2.AArch64.FillKernel.lanes) s fun t =>
      ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps ReferenceMap.changed s t := by
  refine (load_ok s .x1 184 (by decide) (by decide) (h.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s t := keeps.mono (by decide)
  refine ⟨⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩, k⟩
  · rw [k.rd, k.wr, k.regs .x19 (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using h.layout.frameRead 0 (by simp)
  · rw [k.mem, k.regs .x19 (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord

theorem lanes_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) (.block Impl.Argon2.AArch64.FillKernel.lanes)
      (ReferenceMap.Related p pass lane slice index) := by
  have trace := lanes_rel.mono (P' := Related p pass lane slice index)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨lanes_ready s p pass lane slice index h.left, lanes_ready t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .x19 (by decide)).trans
    (hp.bases.trans (hb.2.regs .x19 (by decide)).symm), eq⟩

theorem mapping_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.mapping
      (PointerRelated p lane slice index) := by
  have trace := (lanes_public_rel p pass lane slice index).seq (ReferenceMap.code_rel p pass lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨mapping_ok s p pass lane slice index h.left, mapping_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨hp.left.layout.of_keeps ha.keeps, hp.right.layout.of_keeps hb.keeps,
    hp.left.position.of_keeps ha.keeps, hp.right.position.of_keeps hb.keeps, ?_, ?_, eq⟩
  · exact (ha.keeps.regs .x19 (by decide)).trans (hp.bases.trans (hb.keeps.regs .x19 (by decide)).symm)
  · unfold matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.matrices

theorem matrix_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FillKernel.matrix) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem pointers_trace (p : Params) (lane slice index : Nat) :
    RelCT isa (PointerRelated p lane slice index) Impl.Argon2.AArch64.FillKernel.pointers
      (fun s t => s.sp = t.sp) := by
  have trace := matrix_rel.mono (P' := PointerRelated p lane slice index)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨load_ok s .x4 232 (by decide) (by decide) (h.left.frameRead 232 (by simp)),
      load_ok t .x4 232 (by decide) (by decide) (h.right.frameRead 232 (by simp))⟩)
  have args : RelCT isa (PointerRelated p lane slice index) (.block Impl.Argon2.AArch64.FillKernel.matrix)
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x24, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r) :=
    full.mono (fun _ _ h => h) (by
      intro a b h
      obtain ⟨eq, s, t, hp, ⟨va, ka⟩, ⟨vb, kb⟩⟩ := h
      refine ⟨eq, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact va.trans (hp.matrices.trans vb.symm)
      all_goals rw [ka.regs _ (by decide), kb.regs _ (by decide)]
      · exact hp.leftPosition.current.trans hp.rightPosition.current.symm
      · exact hp.leftPosition.laneLength.trans hp.rightPosition.laneLength.symm
      · exact hp.leftPosition.segmentLength.trans hp.rightPosition.segmentLength.symm
      · exact hp.leftPosition.slice.trans hp.rightPosition.slice.symm
      · exact hp.leftPosition.index.trans hp.rightPosition.index.symm)
  exact (args.seq FillPointers.code_rel).mono (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Merged from `Proof.Argon2.AArch64.FillKernelCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillCompressOperationCT`. -/
section
/-! Only the compression argument addresses, public frame words and stack
pointer determine the compression-and-write trace. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress

structure Related (s t : State) : Prop where
  left : OperationReady s
  right : OperationReady t
  args : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x19], s.gpr r = t.gpr r
  dest : destination s = destination t
  counter : pass s = pass t
  sp : s.sp = t.sp

structure BeforeWrite (s t : State) : Prop where
  leftRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  rightRead : ∀ d ∈ [0, 16, 248], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8
  bases : s.gpr .x19 = t.gpr .x19
  sp : s.sp = t.sp
  words : ∀ d ∈ [0, 16, 248],
    s.mem.readW (off (s.gpr .x19) d) 64 = t.mem.readW (off (t.gpr .x19) d) 64

theorem called_public {s t a b : State} (hp : Related s t)
    (ha : Called s a) (hb : Called t b) : BeforeWrite a b := by
  have abp : a.gpr .x19 = s.gpr .x19 := ha.regs .x19 (by simp [loopRegs])
  have bbp : b.gpr .x19 = t.gpr .x19 := hb.regs .x19 (by simp [loopRegs])
  refine ⟨?_, ?_, abp.trans ((hp.args .x19 (by simp)).trans bbp.symm), ha.sp.trans (hp.sp.trans hb.sp.symm), ?_⟩
  · intro d hd
    rw [ha.rd, ha.wr, abp]; exact hp.left.frameRead d hd
  · intro d hd
    rw [hb.rd, hb.wr, bbp]; exact hp.right.frameRead d hd
  · intro d hd
    rw [abp, bbp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rw [frame_word hp.left ha 0 (by decide), frame_word hp.right hb 0 (by decide)]
      exact hp.counter
    · rw [frame_word hp.left ha 16 (by decide), frame_word hp.right hb 16 (by decide)]
      exact hp.dest
    · rw [frame_word hp.left ha 248 (by decide), frame_word hp.right hb 248 (by decide),
        hp.left.workWord, hp.right.workWord]
      exact hp.args .x3 (by simp)

theorem call_public_rel : RelCT isa Related
    (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.AArch64.compress) BeforeWrite := by
  have trace := call_rel Spec.Argon2.compressApi.name (P := Related) (fun _ _ hp =>
    ⟨hp.left.call, hp.right.call, hp.args .x0 (by simp), hp.args .x1 (by simp),
      hp.args .x2 (by simp), hp.args .x3 (by simp), hp.sp⟩)
  have full := trace.wpDep (fun s t hp =>
    ⟨call_ok _ s hp.left.call, call_ok _ t hp.right.call⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact called_public hp ha hb

theorem writeArgs_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block writeArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem writeArgs_public_rel : RelCT isa BeforeWrite (.block writeArgs)
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x0, .x1], s.gpr r = t.gpr r) := by
  have trace := writeArgs_rel.mono (P' := BeforeWrite) (fun _ _ h => ⟨h.bases, h.sp⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨writeArgs_ok s (hp.leftRead 16 (by simp)) (hp.leftRead 248 (by simp)) (hp.leftRead 0 (by simp)),
      writeArgs_ok t (hp.rightRead 16 (by simp)) (hp.rightRead 248 (by simp)) (hp.rightRead 0 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha.2.2.1.trans ((hp.words 0 (by simp)).trans hb.2.2.1.symm)
  · exact ha.1.trans ((hp.words 16 (by simp)).trans hb.1.symm)
  · exact ha.2.1.trans ((congrArg (· + (4096 : Addr)) (hp.words 248 (by simp))).trans hb.2.1.symm)

theorem operation_rel : RelCT isa Related operation (fun s t => s.sp = t.sp) :=
  call_public_rel.seq (writeArgs_public_rel.seq FillWrite.code_rel)

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Merged from `Proof.Argon2.AArch64.FillCompressCT`. -/
section
/-! Compose the setup trace with compression and the full block write. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress

structure CodeRelated (s t : State) : Prop where
  left : Ready s
  right : Ready t
  args : ∀ r ∈ [Reg.x0, .x1, .x6, .x19], s.gpr r = t.gpr r
  scratch : work s = work t
  counter : pass s = pass t
  sp : s.sp = t.sp

theorem setup_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    setup (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepared_public {s t a b : State} (h : CodeRelated s t)
    (ha : Prepared s a) (hb : Prepared t b) : Related a b := by
  refine ⟨ha.ready, hb.ready, ?_, ha.dest.trans ((h.args .x6 (by simp)).trans hb.dest.symm),
    ha.counter.trans (h.counter.trans hb.counter.symm), ha.sp.trans (h.sp.trans hb.sp.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((h.args .x0 (by simp)).trans hb.left.symm)
  · exact ha.right.trans ((h.args .x1 (by simp)).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (· + (4096 : Addr)) h.scratch).trans hb.output.symm)
  · exact ha.scratch.trans (h.scratch.trans hb.scratch.symm)
  · exact (ha.regs .x19 (by simp [loopRegs])).trans
      ((h.args .x19 (by simp)).trans (hb.regs .x19 (by simp [loopRegs])).symm)

theorem setup_public_rel : RelCT isa CodeRelated setup Related := by
  have trace := setup_rel.mono (P' := CodeRelated)
    (fun _ _ h => ⟨h.args .x19 (by simp), h.sp⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨setup_ok s h.left, setup_ok t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact prepared_public hp ha hb

theorem code_rel : RelCT isa CodeRelated code (fun s t => s.sp = t.sp) :=
  setup_public_rel.seq operation_rel

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Equal permitted references give equal compression and block-update traces. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem prepared_public {p : Params} {pass lane slice index : Nat} {s t a b : State}
    (h : Related p pass lane slice index s t)
    (ha : Prepared s a p pass lane slice index) (hb : Prepared t b p pass lane slice index) :
    FillCompress.CodeRelated a b := by
  have currentEq : current s p lane slice index = current t p lane slice index := by
    unfold current; rw [h.matrices]
  have previousEq : previous s p lane slice index = previous t p lane slice index := by
    unfold previous; rw [h.matrices]
  have referenceEq : referenced s p pass lane slice index = referenced t p pass lane slice index := by
    unfold referenced; rw [h.references, h.matrices]
  have workA : FillCompress.work a = work s := by
    unfold FillCompress.work work; rw [ha.keeps.regs .x19 (by decide), ha.keeps.mem]
  have workB : FillCompress.work b = work t := by
    unfold FillCompress.work work; rw [hb.keeps.regs .x19 (by decide), hb.keeps.mem]
  have passA : FillCompress.pass a = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [ha.keeps.regs .x19 (by decide), ha.keeps.mem]
    exact h.left.passWord
  have passB : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [hb.keeps.regs .x19 (by decide), hb.keeps.mem]
    exact h.right.passWord
  refine ⟨ha.ready, hb.ready, ?_, workA.trans (h.scratch.trans workB.symm), passA.trans passB.symm, ha.keeps.sp.trans (h.stacks.trans hb.keeps.sp.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha.previousPtr.trans (previousEq.trans hb.previousPtr.symm)
  · exact ha.referencePtr.trans (referenceEq.trans hb.referencePtr.symm)
  · exact ha.currentPtr.trans (currentEq.trans hb.currentPtr.symm)
  · exact (ha.keeps.regs .x19 (by decide)).trans (h.bases.trans (hb.keeps.regs .x19 (by decide)).symm)

theorem prepare_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.prepare
      FillCompress.CodeRelated := by
  have trace := (mapping_public_rel p pass lane slice index).seq (pointers_trace p lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨prepare_ok s p pass lane slice index h.left, prepare_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact prepared_public hp ha hb

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.code
      (fun s t => s.sp = t.sp) := (prepare_public_rel p pass lane slice index).seq FillCompress.code_rel

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Merged from `Proof.Argon2.AArch64.FillBlockCounter`. -/
section
/-! Compression preserves the public cache counter selected by the random source. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

theorem counter_run {s t : State} {trace : List Leak} {p : Params} {pass lane slice index old : Nat}
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (run : Exec isa Impl.Argon2.AArch64.FillBlock.code s trace t) :
    t.mem.readW (off (t.gpr .x19) 8) 64 = RandomSource.counterValue p pass slice index old := by
  cases run with
  | seq sourceRun kernelRun =>
    obtain ⟨_, a', runA, source⟩ := RandomSource.code_ok s p pass lane slice index old h state represented
    obtain ⟨_, rfl⟩ := Exec.det sourceRun runA
    obtain ⟨_, a', counterRun, counter⟩ := RandomSource.counter_ok s p pass lane slice index old h
    obtain ⟨_, rfl⟩ := Exec.det sourceRun counterRun
    obtain ⟨_, ready⟩ := source.ready
    obtain ⟨_, t', runT, done⟩ := FillKernel.code_ok _ p pass lane slice index ready.filling
    obtain ⟨_, rfl⟩ := Exec.det kernelRun runT
    exact (done.frame_word ready.filling 8 (by decide) (by decide)).trans counter

end VG.Proof.Argon2.AArch64.FillBlock
end

/-! Merged from `Proof.Argon2.AArch64.FillBlockCT`. -/
section
/-! An active filling cell leaks only its specified data-dependent reference. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  references : independent p pass slice = false →
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory)

theorem Related.of_indices {p : Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (source : RandomSource.Related p pass lane slice index old s t)
    (leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory)
    (rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory)
    (indices : (fillBlock p pass slice lane index leftState).indices =
      (fillBlock p pass slice lane index rightState).indices) :
    Related p pass lane slice index old leftState rightState s t := by
  refine ⟨source, leftMatrix, rightMatrix, ?_⟩
  intro mode
  rw [Proof.Argon2.FillStep.indices p pass lane slice index leftState source.left.filling.bounds.active,
    Proof.Argon2.FillStep.indices p pass lane slice index rightState source.right.filling.bounds.active] at indices
  simp only [mode, Bool.false_eq_true, ite_false] at indices
  exact (List.cons.inj indices).1

theorem Related.reference_eq {p : Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (h : Related p pass lane slice index old leftState rightState s t) :
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory) := by
  cases mode : independent p pass slice
  · exact h.references mode
  · simp only [Proof.Argon2.FillStep.random, mode, ite_true]

theorem source_public_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice index old leftState rightState)
      Impl.Argon2.AArch64.RandomSource.code (FillKernel.Related p pass lane slice index) := by
  intro s t ta tb a b hp ea eb
  obtain ⟨traces, _⟩ := RandomSource.code_rel p pass lane slice index old _ _ _ _ _ _ hp.source ea eb
  obtain ⟨_, a', runA, ha⟩ := RandomSource.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
  obtain ⟨_, b', runB, hb⟩ := RandomSource.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
  obtain ⟨_, sameA⟩ := Exec.det ea runA
  obtain ⟨_, sameB⟩ := Exec.det eb runB
  subst a'; subst b'
  refine ⟨traces, ?_⟩
  obtain ⟨_, readyA⟩ := ha.ready
  obtain ⟨_, readyB⟩ := hb.ready
  refine ⟨readyA.filling, readyB.filling, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.source.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm)
  · exact ha.sp.trans
      (hp.source.stacks.trans hb.sp.symm)
  · exact (ha.frame_word hp.source.left 232 (by decide) (by decide)).trans
      (hp.source.matrices.trans (hb.frame_word hp.source.right 232 (by decide) (by decide)).symm)
  · exact (ha.frame_word hp.source.left 248 (by decide) (by decide)).trans
      (hp.source.work.trans (hb.frame_word hp.source.right 248 (by decide) (by decide)).symm)
  · rw [ha.random, hb.random]; exact hp.reference_eq

theorem code_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice index old leftState rightState)
      Impl.Argon2.AArch64.FillBlock.code (fun s t => s.sp = t.sp) :=
  (source_public_rel p pass lane slice index old leftState rightState).seq
    (FillKernel.code_rel p pass lane slice index)

end VG.Proof.Argon2.AArch64.FillBlock
end

/-! Public counters and coordinates remain related across a segment iteration. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSegment

theorem advance_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x21, .x23], s.gpr r = t.gpr r)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x21, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass lane slice index : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : ∃ old, RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (FillBlock.Related p pass lane slice index old leftState rightState) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (index + 1 < p.segmentLen →
        NextRelated p pass lane slice (index + 1)
          (fillBlock p pass slice lane index leftState) (fillBlock p pass slice lane index rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA advanceA =>
    cases eb with
    | seq fillB advanceB =>
      obtain ⟨filledTrace, filledSp⟩ := FillBlock.code_rel p pass lane slice index old leftState rightState
        _ _ _ _ _ _ hp fillA fillB
      obtain ⟨_, sa, runA, filledA⟩ := FillBlock.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillBlock.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      obtain ⟨counterA, readyA⟩ := filledA.ready
      obtain ⟨counterB, readyB⟩ := filledB.ready
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ (by
        refine ⟨filledSp, ?_⟩
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact readyA.filling.position.segmentLength.trans readyB.filling.position.segmentLength.symm
        · exact readyA.filling.position.index.trans readyB.filling.position.index.symm) advanceA advanceB
      obtain ⟨_, a', advanceRunA, valueA, flagA, keptA⟩ := advance_nat_ok _ p pass lane slice index readyA.filling
      obtain ⟨_, b', advanceRunB, valueB, flagB, keptB⟩ := advance_nat_ok _ p pass lane slice index readyB.filling
      obtain ⟨_, rfl⟩ := Exec.det advanceA advanceRunA
      obtain ⟨_, rfl⟩ := Exec.det advanceB advanceRunB
      refine ⟨by rw [filledTrace, advancedTrace], flagA.trans flagB.symm, ?_⟩
      intro active
      have nextA := next_ready readyA keptA valueA active
      have nextB := next_ready readyB keptB valueB active
      have counterWordA := FillBlock.counter_run hp.source.left leftState hp.leftMatrix fillA
      have counterWordB := FillBlock.counter_run hp.source.right rightState hp.rightMatrix fillB
      have wordEq : BitVec.ofNat 64 counterA = BitVec.ofNat 64 counterB :=
        readyA.cache.words.counterWord.symm.trans
          (counterWordA.trans (counterWordB.symm.trans readyB.cache.words.counterWord))
      have counters := (ReferenceMap.word_eq counterA counterB readyA.cache.bound readyB.cache.bound).mp wordEq
      subst counterB
      refine ⟨⟨counterA, nextA, nextB, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [keptA.regs .x19 (by decide), keptB.regs .x19 (by decide),
          filledA.regs .x19 (by simp [FillCompress.loopRegs]), filledB.regs .x19 (by simp [FillCompress.loopRegs])]
        exact hp.source.bases
      · rw [keptA.sp, keptB.sp, filledA.sp, filledB.sp]
        exact hp.source.stacks
      · unfold FillKernel.matrix
        rw [keptA.mem, keptB.mem, keptA.regs .x19 (by decide), keptB.regs .x19 (by decide)]
        exact filledA.matrix.trans (hp.source.matrices.trans filledB.matrix.symm)
      · unfold AddressCalls.work
        rw [keptA.mem, keptB.mem, keptA.regs .x19 (by decide), keptB.regs .x19 (by decide)]
        exact filledA.work.trans (hp.source.work.trans filledB.work.symm)
      · unfold FillKernel.matrix
        rw [keptA.mem, keptA.regs .x19 (by decide)]
        exact filledA.represented
      · unfold FillKernel.matrix
        rw [keptB.mem, keptB.regs .x19 (by decide)]
        exact filledB.represented

end VG.Proof.Argon2.AArch64.FillSegment
end

/-! The segment loop exposes only the reviewed segment reference log. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice index count leftState).indices =
    (Proof.Argon2.segment p pass lane slice index count rightState).indices

theorem loop_rel (p : Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    RelCT isa (Related p pass lane slice index count old leftState rightState)
      Impl.Argon2.AArch64.FillSegment.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (index old : Nat) (leftState rightState : FillState),
    index + n = p.segmentLen ∧ 0 < n ∧ Related p pass lane slice index n old leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillSegment.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, counter, ls, rs, endIndex, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have blockRelated : FillBlock.Related p pass lane slice j counter ls rs s t :=
        ⟨hp.source, hp.leftMatrix, hp.rightMatrix,
          Proof.Argon2.segment_first_reference p pass lane slice j n ls rs
            hp.source.left.filling.bounds.active hp.indices⟩
      obtain ⟨trace, flags, next⟩ := body_rel p pass lane slice j counter ls rs _ _ _ _ _ _ blockRelated ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p pass lane slice j counter hp.source.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.segmentLen := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨⟨nextCounter, ready⟩, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at indices
        exact ⟨n, by omega, j + 1, nextCounter, fillBlock p pass slice lane j ls,
          fillBlock p pass slice lane j rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨index, old, leftState, rightState, endIndex, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillSegment
end

/-! Complete segment setup and filling expose only the specified reference log. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Related (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState).indices =
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState).indices

structure PreparedRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  left : FillContext.Ready p pass lane slice (start pass slice) 0 s
  right : FillContext.Ready p pass lane slice (start pass slice) 0 t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice (start pass slice) (p.segmentLen - start pass slice) leftState).indices =
    (Proof.Argon2.segment p pass lane slice (start pass slice) (p.segmentLen - start pass slice) rightState).indices

theorem prepare_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice leftState rightState) prepare
      (PreparedRelated p pass lane slice leftState rightState) := by
  have trace := (prepare_trace p pass lane slice).mono
    (P' := Related p pass lane slice leftState rightState) (fun _ _ h => h.ready) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨prepare_ok s p pass lane slice h.ready.left, prepare_ok t p pass lane slice h.ready.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.context, hb.context, ?_, ?_, ha.matrix.trans (hp.ready.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.ready.work.trans hb.work.symm), ha.represents hp.ready.left leftState.memory hp.leftMatrix,
    hb.represents hp.ready.right rightState.memory hp.rightMatrix, ?_⟩
  · rw [ha.regs .x19 (by simp [FillCompress.loopRegs]) (by decide), hb.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)]
    exact hp.ready.bases
  · rw [ha.sp, hb.sp]
    exact hp.ready.stacks
  · have indices := hp.indices
    rw [Proof.Argon2.segment_start p pass lane slice leftState hp.ready.left.parameters.segment_bound.1,
      Proof.Argon2.segment_start p pass lane slice rightState hp.ready.right.parameters.segment_bound.1] at indices
    exact indices

theorem PreparedRelated.of_keeps {p : Params} {pass lane slice : Nat} {leftState rightState : FillState}
    {s t a b : State} (h : PreparedRelated p pass lane slice leftState rightState s t)
    (ka : Divide.Keeps [.x14, .x15] s a) (kb : Divide.Keeps [.x14, .x15] t b) :
    PreparedRelated p pass lane slice leftState rightState a b := by
  refine ⟨h.left.of_keeps (ka.mono (by decide)), h.right.of_keeps (kb.mono (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, h.indices⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.work
  · unfold FillKernel.matrix; rw [ka.mem, ka.regs .x19 (by decide)]; exact h.leftMatrix
  · unfold FillKernel.matrix; rw [kb.mem, kb.regs .x19 (by decide)]; exact h.rightMatrix

theorem check_context_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : FillContext.Ready p pass lane slice (start pass slice) 0 s) : WP isa (.block check) s fun t =>
      eval (.nonzero .x .x14) t = some (decide (start pass slice < p.segmentLen)) ∧ Divide.Keeps [.x14, .x15] s t := by
  have minimum := h.parameters.segment_bound
  have segmentBound : p.segmentLen < 2 ^ 63 := by
    have laneLe : p.laneLen ≤ p.blocks := by
      rw [Proof.Argon2.blocks_lanes p h.parameters.lanesPositive]
      exact Nat.le_mul_of_pos_left _ h.parameters.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.parameters.lanesPositive
    have blocks := Proof.Argon2.blocks_le_memory p
    have memoryBound := h.parameters.memoryBound
    omega
  have startBound := Nat.lt_of_le_of_lt (start_le pass slice p.segmentLen minimum.1) segmentBound
  have left : (s.gpr .x23).toNat < 2 ^ 63 := by
    rw [h.position.index, ReferenceMap.word_nat _ (Nat.lt_trans startBound (by decide))]; exact startBound
  have right : (s.gpr .x21).toNat < 2 ^ 63 := by
    rw [h.position.segmentLength, ReferenceMap.word_nat _ minimum.2]; exact segmentBound
  refine (check_ok s left right).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨?_, keeps⟩
  rw [flag, h.position.index, h.position.segmentLength,
    ReferenceMap.word_nat (start pass slice) (Nat.lt_of_le_of_lt (start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem check_trace : RelCT isa (fun s t : State => s.sp = t.sp)
    (.block check) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem check_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (PreparedRelated p pass lane slice leftState rightState) (.block check)
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        eval (.nonzero .x .x14) s = some (decide (start pass slice < p.segmentLen)) ∧ eval (.nonzero .x .x14) t = some (decide (start pass slice < p.segmentLen))) := by
  have trace := check_trace.mono (P' := PreparedRelated p pass lane slice leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨check_context_ok s p pass lane slice h.left, check_context_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa, fb⟩

theorem code_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice leftState rightState) code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        eval (.nonzero .x .x14) s = some (decide (start pass slice < p.segmentLen)) ∧ eval (.nonzero .x .x14) t = some (decide (start pass slice < p.segmentLen)))
      (.ite (.nonzero .x .x14) Impl.Argon2.AArch64.FillSegment.loop (.block [])) (fun _ _ => True) := by
    refine RelCT.ite (by intro s t h; simp only [h.2.1, h.2.2]) ?_ ?_
    · intro s t ts tt a b hp ea eb
      have active : start pass slice < p.segmentLen := by
        have taken := hp.2
        simp only [hp.1.2.1, Option.some.injEq, decide_eq_true_eq] at taken
        exact taken
      have left := hp.1.1.left.activate active (start_active pass slice)
      have right := hp.1.1.right.activate active (start_active pass slice)
      have related : FillSegment.Related p pass lane slice (start pass slice)
          (p.segmentLen - start pass slice) 0 leftState rightState s t :=
        ⟨⟨left, right, hp.1.1.bases, hp.1.1.stacks, hp.1.1.matrices, hp.1.1.work⟩,
          hp.1.1.leftMatrix, hp.1.1.rightMatrix, hp.1.1.indices⟩
      exact FillSegment.loop_rel p pass lane slice (start pass slice) (p.segmentLen - start pass slice) 0
        leftState rightState (by omega) (by omega) _ _ _ _ _ _ related ea eb
    · intro s t ts tt a b hp ea eb
      cases ea with
      | block runA =>
        cases eb with
        | block runB =>
          obtain ⟨rfl, rfl⟩ := runA
          obtain ⟨rfl, rfl⟩ := runB
          exact ⟨rfl, trivial⟩
  exact (prepare_public_rel p pass lane slice leftState rightState).seq
    ((check_public_rel p pass lane slice leftState rightState).seq branches)

end VG.Proof.Argon2.AArch64.SegmentSetup

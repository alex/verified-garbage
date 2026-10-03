import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillSegment
import VerifiedGarbage.Proof.Argon2.SegmentIndices
import VerifiedGarbage.Proof.Argon2.X86_64.FillSegmentBody
import VerifiedGarbage.Proof.Argon2.X86_64.FillBlock
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressOperation
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelPrepare
import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite
import VerifiedGarbage.Proof.Argon2.X86_64.RandomSourcePrepare
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheSelect
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheWord
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsPrepare
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCalls
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit
import VerifiedGarbage.Impl.Argon2.X86_64.AddressMode
import VerifiedGarbage.Proof.Argon2.X86_64.DependentWord
import VerifiedGarbage.Impl.Argon2.X86_64.DependentWord
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall
import VerifiedGarbage.Proof.Argon2.X86_64.RandomSource
import VerifiedGarbage.Proof.Argon2.X86_64.Relative
import VerifiedGarbage.Proof.Argon2.X86_64.Wrap
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapLane
import VerifiedGarbage.Impl.Argon2.X86_64.FirstLane
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceCount
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupPrepare

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupTrace`. -/
section
/-! Cache reset and initial-index selection branch only on public parameters. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure RelatedReady (p : Params) (pass lane slice : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice s
  right : Ready p pass lane slice t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem RelatedReady.of_keeps {p : Params} {pass lane slice : Nat} {s t a b : State}
    (h : RelatedReady p pass lane slice s t)
    (ka : Divide.Keeps [.rax, .rcx, .r15] s a) (kb : Divide.Keeps [.rax, .rcx, .r15] t b) :
    RelatedReady p pass lane slice a b := by
  have protectedRegs : ∀ r ∈ [Reg.rbp, .rsp, .rbx, .r12, .r13, .r14], r ∉ [Reg.rax, .rcx, .r15] := by decide
  refine ⟨h.left.of_state (fun r hr => ka.regs r (protectedRegs r hr)) ka.mem ka.rd ka.wr,
    h.right.of_state (fun r hr => kb.regs r (protectedRegs r hr)) kb.mem kb.rd kb.wr, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .rbp (by decide), kb.regs .rbp (by decide)]; exact h.bases
  · rw [ka.regs .rsp (by decide), kb.regs .rsp (by decide)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.work

theorem reset_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) reset (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem reset_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) reset (RelatedReady p pass lane slice) := by
  have trace := reset_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨reset_ok s p pass lane slice h.left, reset_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.ready, hb.ready, ?_, ?_, ha.matrix.trans (hp.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩
  · rw [ha.regs .rbp (by simp [calleeSaved]), hb.regs .rbp (by simp [calleeSaved])]; exact hp.bases
  · rw [ha.regs .rsp (by simp [calleeSaved]), hb.regs .rsp (by simp [calleeSaved])]; exact hp.stacks

theorem first_spec_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa (.block first) s fun t => t.zf = decide (pass = 0 ∧ slice = 0) ∧ Divide.Keeps [.rcx] s t := by
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

theorem first_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) (.block first) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem first_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) (.block first)
      (fun s t => RelatedReady p pass lane slice s t ∧ s.zf = t.zf) := by
  have trace := first_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨first_spec_ok s p pass lane slice h.left, first_spec_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps (ka.mono (by decide)) (kb.mono (by decide)), fa.trans fb.symm⟩

theorem index_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) index (fun _ _ => True) := by
  have two : RelCT isa (fun _ _ : State => True) (.block [.mov .r15 (.imm 2)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have zero : RelCT isa (fun _ _ : State => True) (.block [.mov .r15 (.imm 0)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have branches : RelCT isa (fun s t => RelatedReady p pass lane slice s t ∧ s.zf = t.zf)
      (.ite .e (.block [.mov .r15 (.imm 2)]) (.block [.mov .r15 (.imm 0)])) (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, h.2])
      (two.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (zero.mono (fun _ _ _ => trivial) (fun _ _ h => h))
  exact (first_public_rel p pass lane slice).seq branches

theorem prepare_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) prepare (fun _ _ => True) :=
  (reset_public_rel p pass lane slice).seq (index_trace p pass lane slice)

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceStartLit`. -/
section
/-! A checked literal for the chronological reference-window start. -/

namespace VG

materialize_code Impl.Argon2.X86_64.ReferenceStart.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceStartCT`. -/
section
/-! The public pass, slice and segment length determine the window start. -/

namespace VG.Proof.Argon2.X86_64.ReferenceStart

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceStart

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r) code
    (fun s t => s.gpr .r10 = t.gpr .r10) := by
  have h : RelCT isa
      (fun s t => ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r) code
      (fun s t => ∀ r ∈ [Reg.r10], s.gpr r = t.gpr r) :=
    RelCT.taintRegs (τ := Taint.ofRegs [.r9, .r14, .r13])
    (fun _ _ h => Taint.agree_ofRegs h) [Reg.r10] (by taint_decide)
  exact h.mono (fun _ _ h => h) (fun _ _ h => h .r10 (by simp))

end VG.Proof.Argon2.X86_64.ReferenceStart
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapWindowCT`. -/
section
/-! The chronological window branches only on the public pass and slice. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

def PublicPosition (s t : State) : Prop :=
  ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r

theorem window_rel : RelCT isa PublicPosition window (fun _ _ => True) := by
  have start := ReferenceStart.code_rel.wpDep (fun s t _ =>
    ⟨ReferenceStart.code_ok s, ReferenceStart.code_ok t⟩)
  refine start.seq (ReferenceCount.code_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact (ha.2.regs .r9 (by decide)).trans
    ((hp .r9 (by simp)).trans (hb.2.regs .r9 (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapLaneCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FirstLaneLit`. -/
section
/-! A checked literal for the public first-slice lane override. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FirstLane.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.FirstLaneCT`. -/
section
/-! The first-slice override branches only on the public position. -/

namespace VG.Proof.Argon2.X86_64.FirstLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FirstLane

theorem code_rel : RelCT isa
    (fun s t => s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r14 = t.gpr .r14) code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9, .r14])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) (by taint_decide)

end VG.Proof.Argon2.X86_64.FirstLane
end

/-! Recover the public pass from the frame without exposing the secret word. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

def Related (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  Ready p pass lane slice index s ∧ Ready p pass lane slice index t ∧ s.gpr .rbp = t.gpr .rbp

theorem division_keeps (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceLane.code s fun t =>
      Ready p pass lane slice index t ∧ Divide.Keeps changed s t := by
  refine (ReferenceLane.code_ok s
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesPositive)
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesBound)).mono ?_
  rintro t ⟨_, _, keeps⟩
  have k : Divide.Keeps changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .rsi (by decide)), k⟩

theorem division_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index)
      VG.Impl.Argon2.X86_64.ReferenceLane.code (Related p pass lane slice index) := by
  have full := (ReferenceLane.code_secret_rel.mono
    (P' := Related p pass lane slice index) (fun _ _ _ => trivial)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨division_keeps s p pass lane slice index hp.1,
        division_keeps t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .rbp (by decide)).trans
    (hp.2.2.trans (hb.2.regs .rbp (by decide)).symm)⟩

theorem loadPass_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block loadPass) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

def Loaded (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  Related p pass lane slice index s t ∧
    s.gpr .r9 = BitVec.ofNat 64 pass ∧ t.gpr .r9 = BitVec.ofNat 64 pass

theorem loadPass_public (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) : WP isa (.block loadPass) s fun t =>
      Ready p pass lane slice index t ∧ t.gpr .r9 = BitVec.ofNat 64 pass ∧
        Divide.Keeps changed s t := by
  refine (loadPass_ok s ready.passRead).mono ?_
  rintro t ⟨loaded, keeps⟩
  have k : Divide.Keeps changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .rsi (by decide)), loaded.trans ready.passWord, k⟩

theorem loadPass_public_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) (.block loadPass)
      (Loaded p pass lane slice index) := by
  have full := (loadPass_rel.mono (P' := Related p pass lane slice index)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨loadPass_public s p pass lane slice index hp.1,
        loadPass_public t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨⟨ha.1, hb.1, (ha.2.2.regs .rbp (by decide)).trans
    (hp.2.2.trans (hb.2.2.regs .rbp (by decide)).symm)⟩, ha.2.1, hb.2.1⟩

theorem firstLane_loaded_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Loaded p pass lane slice index) VG.Impl.Argon2.X86_64.FirstLane.code
      (Loaded p pass lane slice index) := by
  have trace := FirstLane.code_rel.mono (P' := Loaded p pass lane slice index)
    (fun _ _ hp => ⟨hp.2.1.trans hp.2.2.symm,
      hp.1.1.position.slice.trans hp.1.2.1.position.slice.symm⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t _ => ⟨FirstLane.code_ok s, FirstLane.code_ok t⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  have ka : Divide.Keeps changed s a := ha.2.mono (by decide)
  have kb : Divide.Keeps changed t b := hb.2.mono (by decide)
  refine ⟨⟨hp.1.1.of_keeps ka (ha.2.regs .rsi (by decide)),
    hp.1.2.1.of_keeps kb (hb.2.regs .rsi (by decide)),
    (ka.regs .rbp (by decide)).trans (hp.1.2.2.trans (kb.regs .rbp (by decide)).symm)⟩, ?_, ?_⟩
  · exact (ha.2.regs .r9 (by decide)).trans hp.2.1
  · exact (hb.2.regs .r9 (by decide)).trans hp.2.2

theorem laneArgs_secret_rel : RelCT isa (fun _ _ => True) (.block laneArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem prepareLanes_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) prepareLanes PublicPosition := by
  have head := (division_rel p pass lane slice index).seq
    ((loadPass_public_rel p pass lane slice index).seq (firstLane_loaded_rel p pass lane slice index))
  have trace := head.seq (laneArgs_secret_rel.mono (fun _ _ _ => trivial) (fun _ _ h => h))
  have full := trace.wpDep (fun s t hp =>
    ⟨prepareLanes_ok s p pass lane slice index hp.1,
      prepareLanes_ok t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, _, _, _, ha, hb⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    exact ha.pass.trans hb.pass.symm
  · exact ha.position.slice.trans hb.position.slice.symm
  · exact ha.position.segmentLength.trans hb.position.segmentLength.symm

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapCT`. -/
section
/-! Complete reference mapping has no secret-dependent execution trace. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem relativeArgs_secret_rel :
    RelCT isa (fun _ _ => True) (.block relativeArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem wrapArgs_secret_rel :
    RelCT isa (fun _ _ => True) (.block wrapArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem tail_secret_rel :
    RelCT isa (fun _ _ => True) (.seq relative finish) (fun _ _ => True) :=
  (relativeArgs_secret_rel.seq Relative.code_secret_rel).seq
    (wrapArgs_secret_rel.seq Wrap.code_secret_rel)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun _ _ => True) :=
  (prepareLanes_rel p pass lane slice index).seq (window_rel.seq tail_secret_rel)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.RandomSourceCounter`. -/
section
/-! The stored address counter remains public after either source. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

def counterValue (p : Params) (pass slice index old : Nat) : Addr :=
  BitVec.ofNat 64 (if independent p pass slice then index / 128 + 1 else old)

theorem counter_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) :
    WP isa Impl.Argon2.X86_64.RandomSource.code s fun t =>
      t.mem.readW (off (t.gpr .rbp) 8) 64 = counterValue p pass slice index old := by
  unfold Impl.Argon2.X86_64.RandomSource.code
  refine WP.seq ((prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  refine WP.ite (!independent p pass slice) (by simp only [eval, flag]) ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by cases eq : independent p pass slice <;> simp_all
    refine (DependentWord.code_ok a p pass lane slice index next.filling).mono ?_
    rintro t ⟨_, saved⟩
    unfold counterValue
    simp only [dependent]
    rw [saved.mem, saved.regs .rbp (by decide)]
    exact next.cache.words.counterWord
  · intro mode
    have independent : independent p pass slice = true := by cases eq : independent p pass slice <;> simp_all
    refine (AddressCache.code_ok p pass lane slice old a next.cache.ready).mono ?_
    intro t done
    unfold counterValue
    simp only [independent, ite_true]
    rw [done.selected.counterWord, AddressCache.counter_nat, next.index_nat]

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillCompressCallCT`. -/
section
/-! Compression calls reveal only their argument addresses and stack pointer. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64

theorem call_rel (name : String) {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
      s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .rsp = t.gpr .rsp) :
    RelCT isa P (.call name Impl.Argon2.X86_64.compress) (fun _ _ => True) := by
  apply RelCT.callEx (k := compressLocal) compress_correct compress_ct
  intro s t hp
  obtain ⟨hs, ht, di, si, dx, cx, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := call_hyps s hs
  obtain ⟨pt, ct, wt⟩ := call_hyps t ht
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt, sp⟩
  change s.callEntry.gpr .rdi = t.callEntry.gpr .rdi ∧
    s.callEntry.gpr .rsi = t.callEntry.gpr .rsi ∧
    s.callEntry.gpr .rdx = t.callEntry.gpr .rdx ∧
    s.callEntry.gpr .rcx = t.callEntry.gpr .rcx
  simp only [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
  exact ⟨di, si, dx, cx⟩

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Merged from `Proof.Argon2.X86_64.RandomSourceCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DependentWordLit`. -/
section
/-! Checked literal of the public predecessor-address computation. -/

namespace VG

materialize_code Impl.Argon2.X86_64.DependentWord.pointer

end VG
end

/-! Merged from `Proof.Argon2.X86_64.DependentWordCT`. -/
section
/-! The previous cell is read at an address determined by public parameters. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : FillKernel.Ready p pass lane slice index s
  right : FillKernel.Ready p pass lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : FillKernel.matrix s = FillKernel.matrix t

theorem pointer_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r)
    pointer (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r12, .r13, .r14, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem read_rel : RelCT isa (fun s t => s.gpr .rax = t.gpr .rax) (.block Impl.Argon2.X86_64.DependentWord.read) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rax])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun _ _ => True) := by
  have trace := pointer_rel.mono (P' := Related p pass lane slice index) (by
    intro s t h r hr
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
      (fun s t => s.gpr .rax = t.gpr .rax) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ⟨pa, _⟩, ⟨pb, _⟩⟩ := h
    have equal : FillKernel.previous s p lane slice index = FillKernel.previous t p lane slice index := by
      unfold FillKernel.previous; rw [hp.matrices]
    exact pa.trans (equal.trans pb.symm))
  exact publicTrace.seq read_rel

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Merged from `Proof.Argon2.X86_64.AddressModeLit`. -/
section
/-! Checked literal of the segment addressing-mode computation. -/

namespace VG

materialize_code Impl.Argon2.X86_64.AddressMode.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.AddressModeCT`. -/
section
/-! Mode selection has a fixed trace at the public frame base. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.AddressMode
end

/-! Merged from `Proof.Argon2.X86_64.AddressInputCT`. -/
section
/-! Clearing and header preparation visit fixed offsets of public pointers. -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64

theorem ClearBlock.code_rel : RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi)
    Impl.Argon2.X86_64.ClearBlock.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem AddressHeader.code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rdi, .rbp], s.gpr r = t.gpr r)
    Impl.Argon2.X86_64.AddressHeader.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbp])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64
end

/-! Merged from `Proof.Argon2.X86_64.AddressGenerationCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressCallsCT`. -/
section
/-! The two address-generation compression calls have public fixed addresses. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  work : work s = work t

structure CallRelated (s t : State) : Prop where
  left : FillCompress.CallReady s
  right : FillCompress.CallReady t
  args : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = t.gpr r

theorem first_args_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (args 7168 5120 4096)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem second_args_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (args 7168 4096 6144)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem args_public_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (args x y out)) (fun _ _ => True)) :
    RelCT isa Related (.block (args x y out)) CallRelated := by
  have trace := argTrace.mono (P' := Related) (fun _ _ hp => hp.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨args_nat_ok s hp.left x y out (by omega) (by omega) (by omega),
      args_nat_ok t hp.right x y out (by omega) (by omega) (by omega)⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨args_call_ready s a hp.left x y out hx hy ho bx by_ bo ha,
    args_call_ready t b hp.right x y out hx hy ho bx by_ bo hb, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((congrArg (fun p => off p x) hp.work).trans hb.left.symm)
  · exact ha.right.trans ((congrArg (fun p => off p y) hp.work).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (fun p => off p out) hp.work).trans hb.output.symm)
  · exact ha.scratch.trans (hp.work.trans hb.scratch.symm)
  · exact (ha.keeps.regs .rsp (by decide)).trans
      (hp.stacks.trans (hb.keeps.regs .rsp (by decide)).symm)

theorem stage_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (args x y out)) (fun _ _ => True)) :
    RelCT isa Related (stage x y out) Related := by
  have call := FillCompress.call_rel Spec.Argon2.compressApi.name (P := CallRelated)
    (fun _ _ hp => ⟨hp.left, hp.right, hp.args .rdi (by simp), hp.args .rsi (by simp),
      hp.args .rdx (by simp), hp.args .rcx (by simp), hp.args .rsp (by simp)⟩)
  have trace := (args_public_rel x y out hx hy ho bx by_ bo argTrace).seq call
  have full := trace.wpDep (fun s t hp =>
    ⟨stage_ok s hp.left x y out hx hy ho bx by_ bo,
      stage_ok t hp.right x y out hx hy ho bx by_ bo⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready, hb.ready,
    (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩

theorem calls_rel : RelCT isa Related calls Related :=
  (stage_rel 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) first_args_rel).seq
  (stage_rel 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) second_args_rel)

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Independent-address generation keeps its entire trace independent of secrets. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

theorem Related.of_stable {s t a b : State} (h : Related s t)
    (ha : Stable s a) (hb : Stable t b) : Related a b :=
  ⟨ha.ready, hb.ready,
    (ha.regs .rbp (by simp [calleeSaved])).trans
      (h.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans
      (h.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm),
    ha.work_eq.trans (h.work.trans hb.work_eq.symm)⟩

theorem input_pointer_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (pointer 5120)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem zero_pointer_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (pointer 7168)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

structure PointRelated (s t : State) : Prop where
  related : Related s t
  pointer : s.gpr .rdi = t.gpr .rdi

theorem pointer_public_rel (offset : Nat)
    (trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (pointer offset)) (fun _ _ => True)) :
    RelCT isa Related (.block (pointer offset)) PointRelated := by
  have publicTrace := trace.mono (P' := Related) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := publicTrace.wpDep (fun s t h =>
    ⟨pointer_ok s offset h.left.frameRead, pointer_ok t offset h.right.frameRead⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨pa, ka⟩, ⟨pb, kb⟩⟩ := h
  exact ⟨hp.of_stable (pointer_stable hp.left ka) (pointer_stable hp.right kb),
    pa.trans ((congrArg (· + displacement offset) hp.work).trans pb.symm)⟩

theorem clearAt_rel (offset : Nat) (bound : offset + 1024 ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (pointer offset)) (fun _ _ => True)) :
    RelCT isa Related (clearAt offset) Related := by
  have clear := ClearBlock.code_rel.mono (P' := PointRelated)
    (fun _ _ h => h.pointer) (fun _ _ h => h)
  have blocks := (pointer_public_rel offset trace).seq clear
  have full := blocks.wpDep (fun s t h =>
    ⟨clearAt_ok s h.left offset bound, clearAt_ok t h.right offset bound⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.of_stable (ha.stable bound) (hb.stable bound)

structure PrepareRelated (s t : State) : Prop where
  related : Related s t
  leftReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  rightReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .rbp) d) 8

theorem prepare_rel : RelCT isa PrepareRelated prepare Related := by
  have header := AddressHeader.code_rel.mono (P' := PointRelated) (by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.pointer
    · exact h.related.bases) (fun _ _ h => h)
  have trace := (clearAt_rel 5120 (by decide) input_pointer_rel).seq
    ((clearAt_rel 7168 (by decide) zero_pointer_rel).seq
      ((pointer_public_rel 5120 input_pointer_rel).seq header))
  have narrowed := trace.mono (P' := PrepareRelated) (fun _ _ h => h.related) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨prepare_layout_ok s h.related.left h.leftReads,
      prepare_layout_ok t h.related.right h.rightReads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.related.of_stable ha.stable hb.stable

theorem code_rel : RelCT isa PrepareRelated code Related := prepare_rel.seq calls_rel

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheWordCT`. -/
section
/-! The cached random word is secret; its read address is public. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

structure WordRelated (s t : State) : Prop where
  layout : AddressCalls.Related s t
  indices : s.gpr .r15 = t.gpr .r15

theorem wordArgs_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r15], s.gpr r = t.gpr r)
    (.block wordArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem wordRead_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rcx, .rax], s.gpr r = t.gpr r)
    (.block wordRead) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rcx, .rax])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem word_rel : RelCT isa WordRelated Impl.Argon2.X86_64.AddressCache.word (fun _ _ => True) := by
  have trace := wordArgs_rel.mono (P' := WordRelated) (by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.layout.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨wordArgs_ok s h.layout.left.frameRead, wordArgs_ok t h.layout.right.frameRead⟩)
  have args : RelCT isa WordRelated (.block wordArgs)
      (fun s t => ∀ r ∈ [Reg.rcx, .rax], s.gpr r = t.gpr r) := full.mono (fun _ _ h => h) (by
    intro a b h r hr
    obtain ⟨_, s, t, hp, ⟨sa, ia, _⟩, ⟨sb, ib, _⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sa.trans (hp.layout.work.trans sb.symm)
    · exact ia.trans ((congrArg (· &&& 127) hp.indices).trans ib.symm))
  exact args.seq wordRead_rel

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheSelectCT`. -/
section
/-! Cache regeneration branches only on public counters. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

structure CacheRelated (s t : State) : Prop where
  prepare : AddressCalls.PrepareRelated s t
  indices : s.gpr .r15 = t.gpr .r15
  counters : s.mem.readW (off (s.gpr .rbp) 8) 64 = t.mem.readW (off (t.gpr .rbp) 8) 64
  leftWrite : InRegions s.wr (off (s.gpr .rbp) 8) 8
  rightWrite : InRegions t.wr (off (t.gpr .rbp) 8) 8

structure CheckedRelated (s t : State) : Prop where
  related : CacheRelated s t
  values : s.gpr .rax = t.gpr .rax
  flags : s.zf = t.zf

theorem check_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r15], s.gpr r = t.gpr r)
    (.block check) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem check_public_rel : RelCT isa CacheRelated (.block check) CheckedRelated := by
  have trace := check_rel.mono (P' := CacheRelated) (by
    intro s t h r hr
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
  have index : a.gpr .r15 = b.gpr .r15 := (sa.regs .r15 (by simp [calleeSaved])).trans
    (hp.indices.trans (sb.regs .r15 (by simp [calleeSaved])).symm)
  have counters : a.mem.readW (off (a.gpr .rbp) 8) 64 = b.mem.readW (off (b.gpr .rbp) 8) 64 := by
    rw [ka.mem, kb.mem, sa.regs .rbp (by simp [calleeSaved]), sb.regs .rbp (by simp [calleeSaved])]
    exact hp.counters
  refine ⟨⟨⟨hp.prepare.related.of_stable sa sb, sa.reads hp.prepare.leftReads,
    sb.reads hp.prepare.rightReads⟩, index, counters, ?_, ?_⟩, ?_, ?_⟩
  · rw [ka.wr, sa.regs .rbp (by simp [calleeSaved])]; exact hp.leftWrite
  · rw [kb.wr, sb.regs .rbp (by simp [calleeSaved])]; exact hp.rightWrite
  · rw [va, vb, hp.indices]
  · rw [fa, fb, hp.indices, hp.counters]

theorem save_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block save) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem save_public_rel : RelCT isa CheckedRelated (.block save) AddressCalls.PrepareRelated := by
  have trace := save_rel.mono (P' := CheckedRelated)
    (fun _ _ h => h.related.prepare.related.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨save_ready s h.related.prepare.related.left h.related.leftWrite,
      save_ready t h.related.prepare.related.right h.related.rightWrite⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ha.work_eq.trans
    (hp.related.prepare.related.work.trans hb.work_eq.symm)⟩, ?_, ?_⟩
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.bases
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.stacks
  · rw [ha.rd, ha.wr, ha.regs]; exact hp.related.prepare.leftReads
  · rw [hb.rd, hb.wr, hb.regs]; exact hp.related.prepare.rightReads

theorem select_trace : RelCT isa CacheRelated select (fun _ _ => True) := by
  have noop : RelCT isa (fun _ _ : State => True) (.block []) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have branches : RelCT isa CheckedRelated
      (.ite .e (.block []) (.seq (.block save) Impl.Argon2.X86_64.AddressCalls.code))
      (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, h.flags])
      (noop.mono (fun _ _ _ => trivial) (fun _ _ h => h))
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
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.pubs.prepare.related.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.pubs.prepare.related.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.regs .r15 (by simp [calleeSaved])).trans
      (hp.pubs.indices.trans (hb.regs .r15 (by simp [calleeSaved])).symm)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (ReadyRelated p pass lane slice old) code (fun _ _ => True) :=
  (select_public_rel p pass lane slice old).seq word_rel

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Source dispatch and cached-word selection use only public addresses and guards. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.RandomSource

structure Related (p : Params) (pass lane slice index old : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice index old s
  right : Ready p pass lane slice index old t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem Related.of_keeps {p : Params} {pass lane slice index old : Nat} {s t a b : State}
    (h : Related p pass lane slice index old s t)
    (ka : Divide.Keeps ReferenceMap.changed s a) (kb : Divide.Keeps ReferenceMap.changed t b) :
    Related p pass lane slice index old a b := by
  refine ⟨h.left.of_keeps ka, h.right.of_keeps kb, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .rbp (by decide), kb.regs .rbp (by decide)]; exact h.bases
  · rw [ka.regs .rsp (by decide), kb.regs .rsp (by decide)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.work

theorem test_rel : RelCT isa (fun _ _ : State => True) (.block test) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem prepare_rel (p : Params) (pass lane slice index old : Nat) :
    RelCT isa (Related p pass lane slice index old) prepare
      (fun s t => Related p pass lane slice index old s t ∧ s.zf = t.zf) := by
  have trace := AddressMode.code_rel.seq test_rel
  have narrowed := trace.mono (P' := Related p pass lane slice index old)
    (fun _ _ h => h.bases) (fun _ _ h => h)
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
    RelCT isa (Related p pass lane slice index old) code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => Related p pass lane slice index old s t ∧ s.zf = t.zf)
      (.ite .e Impl.Argon2.X86_64.DependentWord.code Impl.Argon2.X86_64.AddressCache.code)
      (fun _ _ => True) := by
    apply RelCT.ite (by intro s t h; simp only [eval, h.2])
    · exact (DependentWord.code_rel p pass lane slice index).mono
        (fun _ _ h => ⟨h.1.1.left.filling, h.1.1.right.filling, h.1.1.bases, h.1.1.matrices⟩)
        (fun _ _ h => h)
    · exact (AddressCache.code_rel p pass lane slice old).mono
        (fun _ _ h => h.1.1.cache) (fun _ _ h => h)
  exact (prepare_rel p pass lane slice index old).seq branches

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillWriteLit`. -/
section
/-! Checked literal of the complete copy/XOR block write. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FillWrite.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.FillWriteCT`. -/
section
/-! Both write paths have a public, fixed sequence of memory accesses. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillWrite

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r9, .rdi, .rsi], s.gpr r = t.gpr r) code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9, .rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64.FillWrite
end

/-! Merged from `Proof.Argon2.X86_64.FillSegmentCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSegmentBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillPointersCT`. -/
section
/-! The pointer setup only branches on the public current column.
Reference coordinates may differ without changing its execution trace. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r8, .rbx, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r) code
    (fun s t => ∀ r ∈ [Reg.r10], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.r8, .rbx, .r12, .r13, .r14, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) [Reg.r10] (by taint_decide)

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Merged from `Proof.Argon2.X86_64.FillKernelMappingCT`. -/
section
/-! Reference mapping exposes no more than the permitted reference coordinates. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice index s
  right : Ready p pass lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : matrix s = matrix t
  scratch : work s = work t
  references : Spec.Argon2.reference p pass lane slice index (s.gpr .rdi) =
    Spec.Argon2.reference p pass lane slice index (t.gpr .rdi)

structure PointerRelated (p : Params) (lane slice index : Nat) (s t : State) : Prop where
  left : Layout p s
  right : Layout p t
  leftPosition : ReferenceMap.Position p lane slice index s
  rightPosition : ReferenceMap.Position p lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t

theorem lanes_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FillKernel.lanes) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem lanes_ready (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa (.block Impl.Argon2.X86_64.FillKernel.lanes) s fun t =>
      ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps ReferenceMap.changed s t := by
  refine (load_ok s .rsi 184 (h.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s t := keeps.mono (by decide)
  refine ⟨⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩, k⟩
  · rw [k.rd, k.wr, k.regs .rbp (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using h.layout.frameRead 0 (by simp)
  · rw [k.mem, k.regs .rbp (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord

theorem lanes_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) (.block Impl.Argon2.X86_64.FillKernel.lanes)
      (ReferenceMap.Related p pass lane slice index) := by
  have trace := lanes_rel.mono (P' := Related p pass lane slice index)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨lanes_ready s p pass lane slice index h.left, lanes_ready t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .rbp (by decide)).trans
    (hp.bases.trans (hb.2.regs .rbp (by decide)).symm)⟩

theorem mapping_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.X86_64.FillKernel.mapping
      (PointerRelated p lane slice index) := by
  have trace := (lanes_public_rel p pass lane slice index).seq (ReferenceMap.code_rel p pass lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨mapping_ok s p pass lane slice index h.left, mapping_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨hp.left.layout.of_keeps ha.keeps, hp.right.layout.of_keeps hb.keeps,
    hp.left.position.of_keeps ha.keeps, hp.right.position.of_keeps hb.keeps, ?_, ?_⟩
  · exact (ha.keeps.regs .rbp (by decide)).trans (hp.bases.trans (hb.keeps.regs .rbp (by decide)).symm)
  · unfold matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]
    exact hp.matrices

theorem matrix_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FillKernel.matrix) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem pointers_trace (p : Params) (lane slice index : Nat) :
    RelCT isa (PointerRelated p lane slice index) Impl.Argon2.X86_64.FillKernel.pointers
      (fun _ _ => True) := by
  have trace := matrix_rel.mono (P' := PointerRelated p lane slice index)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨load_ok s .r8 232 (h.left.frameRead 232 (by simp)),
      load_ok t .r8 232 (h.right.frameRead 232 (by simp))⟩)
  have args : RelCT isa (PointerRelated p lane slice index) (.block Impl.Argon2.X86_64.FillKernel.matrix)
      (fun s t => ∀ r ∈ [Reg.r8, .rbx, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r) :=
    full.mono (fun _ _ h => h) (by
      intro a b h r hr
      obtain ⟨_, s, t, hp, ⟨va, ka⟩, ⟨vb, kb⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact va.trans (hp.matrices.trans vb.symm)
      all_goals rw [ka.regs _ (by decide), kb.regs _ (by decide)]
      · exact hp.leftPosition.current.trans hp.rightPosition.current.symm
      · exact hp.leftPosition.laneLength.trans hp.rightPosition.laneLength.symm
      · exact hp.leftPosition.segmentLength.trans hp.rightPosition.segmentLength.symm
      · exact hp.leftPosition.slice.trans hp.rightPosition.slice.symm
      · exact hp.leftPosition.index.trans hp.rightPosition.index.symm)
  exact (args.seq FillPointers.code_rel).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Merged from `Proof.Argon2.X86_64.FillKernelCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillCompressOperationCT`. -/
section
/-! Only the compression argument addresses, public frame words and stack
pointer determine the compression-and-write trace. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

structure Related (s t : State) : Prop where
  left : OperationReady s
  right : OperationReady t
  args : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .rbp], s.gpr r = t.gpr r
  dest : destination s = destination t
  counter : pass s = pass t

structure BeforeWrite (s t : State) : Prop where
  leftRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  rightRead : ∀ d ∈ [0, 16, 248], InRegions (t.rd ++ t.wr) (off (t.gpr .rbp) d) 8
  bases : s.gpr .rbp = t.gpr .rbp
  words : ∀ d ∈ [0, 16, 248],
    s.mem.readW (off (s.gpr .rbp) d) 64 = t.mem.readW (off (t.gpr .rbp) d) 64

theorem called_public {s t a b : State} (hp : Related s t)
    (ha : Called s a) (hb : Called t b) : BeforeWrite a b := by
  have abp : a.gpr .rbp = s.gpr .rbp := ha.regs .rbp (by simp [calleeSaved])
  have bbp : b.gpr .rbp = t.gpr .rbp := hb.regs .rbp (by simp [calleeSaved])
  refine ⟨?_, ?_, abp.trans ((hp.args .rbp (by simp)).trans bbp.symm), ?_⟩
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
      exact hp.args .rcx (by simp)

theorem call_public_rel : RelCT isa Related
    (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.X86_64.compress) BeforeWrite := by
  have trace := call_rel Spec.Argon2.compressApi.name (P := Related) (fun _ _ hp =>
    ⟨hp.left.call, hp.right.call, hp.args .rdi (by simp), hp.args .rsi (by simp),
      hp.args .rdx (by simp), hp.args .rcx (by simp), hp.args .rsp (by simp)⟩)
  have full := trace.wpDep (fun s t hp =>
    ⟨call_ok _ s hp.left.call, call_ok _ t hp.right.call⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact called_public hp ha hb

theorem writeArgs_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block writeArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem writeArgs_public_rel : RelCT isa BeforeWrite (.block writeArgs)
    (fun s t => ∀ r ∈ [Reg.r9, .rdi, .rsi], s.gpr r = t.gpr r) := by
  have trace := writeArgs_rel.mono (P' := BeforeWrite) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨writeArgs_ok s (hp.leftRead 16 (by simp)) (hp.leftRead 248 (by simp)) (hp.leftRead 0 (by simp)),
      writeArgs_ok t (hp.rightRead 16 (by simp)) (hp.rightRead 248 (by simp)) (hp.rightRead 0 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha.2.2.1.trans ((hp.words 0 (by simp)).trans hb.2.2.1.symm)
  · exact ha.1.trans ((hp.words 16 (by simp)).trans hb.1.symm)
  · exact ha.2.1.trans ((congrArg (· + (4096 : Addr)) (hp.words 248 (by simp))).trans hb.2.1.symm)

theorem operation_rel : RelCT isa Related operation (fun _ _ => True) :=
  call_public_rel.seq (writeArgs_public_rel.seq FillWrite.code_rel)

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Merged from `Proof.Argon2.X86_64.FillCompressCT`. -/
section
/-! Compose the setup trace with compression and the full block write. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

structure CodeRelated (s t : State) : Prop where
  left : Ready s
  right : Ready t
  args : ∀ r ∈ [Reg.rdi, .rsi, .r10, .rsp, .rbp], s.gpr r = t.gpr r
  scratch : work s = work t
  counter : pass s = pass t

theorem setup_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    setup (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem prepared_public {s t a b : State} (h : CodeRelated s t)
    (ha : Prepared s a) (hb : Prepared t b) : Related a b := by
  refine ⟨ha.ready, hb.ready, ?_, ha.dest.trans ((h.args .r10 (by simp)).trans hb.dest.symm),
    ha.counter.trans (h.counter.trans hb.counter.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((h.args .rdi (by simp)).trans hb.left.symm)
  · exact ha.right.trans ((h.args .rsi (by simp)).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (· + (4096 : Addr)) h.scratch).trans hb.output.symm)
  · exact ha.scratch.trans (h.scratch.trans hb.scratch.symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      ((h.args .rsp (by simp)).trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      ((h.args .rbp (by simp)).trans (hb.regs .rbp (by simp [calleeSaved])).symm)

theorem setup_public_rel : RelCT isa CodeRelated setup Related := by
  have trace := setup_rel.mono (P' := CodeRelated)
    (fun _ _ h => h.args .rbp (by simp)) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨setup_ok s h.left, setup_ok t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact prepared_public hp ha hb

theorem code_rel : RelCT isa CodeRelated code (fun _ _ => True) :=
  setup_public_rel.seq operation_rel

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Equal permitted references give equal compression and block-update traces. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

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
    unfold FillCompress.work work; rw [ha.keeps.regs .rbp (by decide), ha.keeps.mem]
  have workB : FillCompress.work b = work t := by
    unfold FillCompress.work work; rw [hb.keeps.regs .rbp (by decide), hb.keeps.mem]
  have passA : FillCompress.pass a = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [ha.keeps.regs .rbp (by decide), ha.keeps.mem]
    exact h.left.passWord
  have passB : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [hb.keeps.regs .rbp (by decide), hb.keeps.mem]
    exact h.right.passWord
  refine ⟨ha.ready, hb.ready, ?_, workA.trans (h.scratch.trans workB.symm), passA.trans passB.symm⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.previousPtr.trans (previousEq.trans hb.previousPtr.symm)
  · exact ha.referencePtr.trans (referenceEq.trans hb.referencePtr.symm)
  · exact ha.currentPtr.trans (currentEq.trans hb.currentPtr.symm)
  · exact (ha.keeps.regs .rsp (by decide)).trans (h.stacks.trans (hb.keeps.regs .rsp (by decide)).symm)
  · exact (ha.keeps.regs .rbp (by decide)).trans (h.bases.trans (hb.keeps.regs .rbp (by decide)).symm)

theorem prepare_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.X86_64.FillKernel.prepare
      FillCompress.CodeRelated := by
  have trace := (mapping_public_rel p pass lane slice index).seq (pointers_trace p lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨prepare_ok s p pass lane slice index h.left, prepare_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact prepared_public hp ha hb

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.X86_64.FillKernel.code
      (fun _ _ => True) := (prepare_public_rel p pass lane slice index).seq FillCompress.code_rel

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Merged from `Proof.Argon2.X86_64.FillBlockCounter`. -/
section
/-! Compression preserves the public cache counter selected by the random source. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

theorem counter_run {s t : State} {trace : List Leak} {p : Params} {pass lane slice index old : Nat}
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (run : Exec isa Impl.Argon2.X86_64.FillBlock.code s trace t) :
    t.mem.readW (off (t.gpr .rbp) 8) 64 = RandomSource.counterValue p pass slice index old := by
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

end VG.Proof.Argon2.X86_64.FillBlock
end

/-! Merged from `Proof.Argon2.X86_64.FillBlockCT`. -/
section
/-! An active filling cell leaks only its specified data-dependent reference. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

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
      Impl.Argon2.X86_64.RandomSource.code (FillKernel.Related p pass lane slice index) := by
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
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.source.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.source.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.frame_word hp.source.left 232 (by decide) (by decide)).trans
      (hp.source.matrices.trans (hb.frame_word hp.source.right 232 (by decide) (by decide)).symm)
  · exact (ha.frame_word hp.source.left 248 (by decide) (by decide)).trans
      (hp.source.work.trans (hb.frame_word hp.source.right 248 (by decide) (by decide)).symm)
  · rw [ha.random, hb.random]; exact hp.reference_eq

theorem code_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice index old leftState rightState)
      Impl.Argon2.X86_64.FillBlock.code (fun _ _ => True) :=
  (source_public_rel p pass lane slice index old leftState rightState).seq
    (FillKernel.code_rel p pass lane slice index)

end VG.Proof.Argon2.X86_64.FillBlock
end

/-! Public counters and coordinates remain related across a segment iteration. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSegment

theorem advance_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r13, .r15], s.gpr r = t.gpr r)
    (.block advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r13, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

structure NextRelated (p : Params) (pass lane slice index : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : ∃ old, RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (FillBlock.Related p pass lane slice index old leftState rightState) body
      (fun s t => s.cf = t.cf ∧ (index + 1 < p.segmentLen →
        NextRelated p pass lane slice (index + 1)
          (fillBlock p pass slice lane index leftState) (fillBlock p pass slice lane index rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA advanceA =>
    cases eb with
    | seq fillB advanceB =>
      obtain ⟨filledTrace, _⟩ := FillBlock.code_rel p pass lane slice index old leftState rightState
        _ _ _ _ _ _ hp fillA fillB
      obtain ⟨_, sa, runA, filledA⟩ := FillBlock.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillBlock.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      obtain ⟨counterA, readyA⟩ := filledA.ready
      obtain ⟨counterB, readyB⟩ := filledB.ready
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ (by
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
      · rw [keptA.regs .rbp (by decide), keptB.regs .rbp (by decide),
          filledA.regs .rbp (by simp [calleeSaved]), filledB.regs .rbp (by simp [calleeSaved])]
        exact hp.source.bases
      · rw [keptA.regs .rsp (by decide), keptB.regs .rsp (by decide),
          filledA.regs .rsp (by simp [calleeSaved]), filledB.regs .rsp (by simp [calleeSaved])]
        exact hp.source.stacks
      · unfold FillKernel.matrix
        rw [keptA.mem, keptB.mem, keptA.regs .rbp (by decide), keptB.regs .rbp (by decide)]
        exact filledA.matrix.trans (hp.source.matrices.trans filledB.matrix.symm)
      · unfold AddressCalls.work
        rw [keptA.mem, keptB.mem, keptA.regs .rbp (by decide), keptB.regs .rbp (by decide)]
        exact filledA.work.trans (hp.source.work.trans filledB.work.symm)
      · unfold FillKernel.matrix
        rw [keptA.mem, keptA.regs .rbp (by decide)]
        exact filledA.represented
      · unfold FillKernel.matrix
        rw [keptB.mem, keptB.regs .rbp (by decide)]
        exact filledB.represented

end VG.Proof.Argon2.X86_64.FillSegment
end

/-! The segment loop exposes only the reviewed segment reference log. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

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
      Impl.Argon2.X86_64.FillSegment.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (index old : Nat) (leftState rightState : FillState),
    index + n = p.segmentLen ∧ 0 < n ∧ Related p pass lane slice index n old leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillSegment.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
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
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.segmentLen := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨⟨nextCounter, ready⟩, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at indices
        exact ⟨n, by omega, j + 1, nextCounter, fillBlock p pass slice lane j ls,
          fillBlock p pass slice lane j rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨index, old, leftState, rightState, endIndex, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.FillSegment
end

/-! Complete segment setup and filling expose only the specified reference log. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

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
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
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
  · rw [ha.regs .rbp (by simp [calleeSaved]) (by decide), hb.regs .rbp (by simp [calleeSaved]) (by decide)]
    exact hp.ready.bases
  · rw [ha.regs .rsp (by simp [calleeSaved]) (by decide), hb.regs .rsp (by simp [calleeSaved]) (by decide)]
    exact hp.ready.stacks
  · have indices := hp.indices
    rw [Proof.Argon2.segment_start p pass lane slice leftState hp.ready.left.parameters.segment_bound.1,
      Proof.Argon2.segment_start p pass lane slice rightState hp.ready.right.parameters.segment_bound.1] at indices
    exact indices

theorem PreparedRelated.of_keeps {p : Params} {pass lane slice : Nat} {leftState rightState : FillState}
    {s t a b : State} (h : PreparedRelated p pass lane slice leftState rightState s t)
    (ka : Divide.Keeps [] s a) (kb : Divide.Keeps [] t b) :
    PreparedRelated p pass lane slice leftState rightState a b := by
  refine ⟨h.left.of_keeps (ka.mono (by decide)), h.right.of_keeps (kb.mono (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, h.indices⟩
  · rw [ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.bases
  · rw [ka.regs .rsp (by simp), kb.regs .rsp (by simp)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.work
  · unfold FillKernel.matrix; rw [ka.mem, ka.regs .rbp (by simp)]; exact h.leftMatrix
  · unfold FillKernel.matrix; rw [kb.mem, kb.regs .rbp (by simp)]; exact h.rightMatrix

theorem check_context_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : FillContext.Ready p pass lane slice (start pass slice) 0 s) : WP isa (.block check) s fun t =>
      t.cf = decide (start pass slice < p.segmentLen) ∧ Divide.Keeps [] s t := by
  refine (check_ok s).mono ?_
  rintro t ⟨flag, keeps⟩
  have minimum := h.parameters.segment_bound
  refine ⟨?_, keeps⟩
  rw [flag, h.position.index, h.position.segmentLength,
    ReferenceMap.word_nat (start pass slice) (Nat.lt_of_le_of_lt (start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem check_trace : RelCT isa (fun _ _ : State => True) (.block check) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem check_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (PreparedRelated p pass lane slice leftState rightState) (.block check)
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        s.cf = decide (start pass slice < p.segmentLen) ∧ t.cf = decide (start pass slice < p.segmentLen)) := by
  have trace := check_trace.mono (P' := PreparedRelated p pass lane slice leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨check_context_ok s p pass lane slice h.left, check_context_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa, fb⟩

theorem code_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice leftState rightState) code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        s.cf = decide (start pass slice < p.segmentLen) ∧ t.cf = decide (start pass slice < p.segmentLen))
      (.ite .b Impl.Argon2.X86_64.FillSegment.loop (.block [])) (fun _ _ => True) := by
    refine RelCT.ite (by intro s t h; simp only [eval, h.2.1, h.2.2]) ?_ ?_
    · intro s t ts tt a b hp ea eb
      have active : start pass slice < p.segmentLen := by
        have taken := hp.2
        simp only [eval, hp.1.2.1, Option.some.injEq, decide_eq_true_eq] at taken
        exact taken
      have left := hp.1.1.left.activate active (start_active pass slice)
      have right := hp.1.1.right.activate active (start_active pass slice)
      have related : FillSegment.Related p pass lane slice (start pass slice)
          (p.segmentLen - start pass slice) 0 leftState rightState s t :=
        ⟨⟨left, right, hp.1.1.bases, hp.1.1.stacks, hp.1.1.matrices, hp.1.1.work⟩,
          hp.1.1.leftMatrix, hp.1.1.rightMatrix, hp.1.1.indices⟩
      exact FillSegment.loop_rel p pass lane slice (start pass slice) (p.segmentLen - start pass slice) 0
        leftState rightState (by omega) (by omega) _ _ _ _ _ _ related ea eb
    · have noop : RelCT isa (fun _ _ : State => True) (.block []) (fun _ _ => True) :=
        RelCT.taint (A := taint) (Taint.ofRegs [])
          (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
      exact noop.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  exact (prepare_public_rel p pass lane slice leftState rightState).seq
    ((check_public_rel p pass lane slice leftState rightState).seq branches)

end VG.Proof.Argon2.X86_64.SegmentSetup

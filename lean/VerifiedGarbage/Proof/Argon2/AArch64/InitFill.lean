import VerifiedGarbage.Impl.Argon2.AArch64.InitFill
import VerifiedGarbage.Proof.Argon2.AArch64.InitFillFrames

/-! Exact initialization, every filling pass, final reduction and H′ after the reviewed H₀. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def result (p : Params) (h0 : List Byte) : List Byte :=
  Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes (initMemory p h0)).memory

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = result p (bytesAt s.mem (s.gpr .x19) 64)
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem writes_eq (s t : State) (p : Params) (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (base : FillKernel.matrix t = FillKernel.matrix s) (work : FinalOutput.work t = FinalOutput.work s)
    (output : FinalOutput.output t = FinalOutput.output s) : writes t p = writes s p := by
  unfold writes
  rw [bp, sp, base, work, output]

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params) (h : Ready p s) :
    WP isa (Impl.Argon2.AArch64.InitFill.code name v.hash) s (Done s · p) := by
  have params := h.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have blocks := Proof.Argon2.lastIndex_bounds p params.lanesPositive params.segment_bound.1 0 params.lanesPositive
  unfold Impl.Argon2.AArch64.InitFill.code
  refine WP.seq ((MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen h.initializing
    params.lanesPositive (Nat.lt_trans params.lanesBound (by decide)) q).mono ?_)
  intro a initialized
  have setupReady := initialized_setup h initialized
  have initializedBase : FillKernel.matrix a = FillKernel.matrix s :=
    initialized.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have initializedWork : FinalOutput.work a = FinalOutput.work s :=
    initialized.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have initializedOutput : FinalOutput.output a = FinalOutput.output s :=
    initialized.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have rep : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks
      (initMemory p (bytesAt s.mem (s.gpr .x19) 64)).memory := by
    rw [initializedBase]
    exact initialized.initialized.represents params.lanesPositive (by omega)
  refine WP.seq ((FillSetup.code_ok a p setupReady).mono ?_)
  intro b prepared
  refine (FillFinish.code_ok v name b p (prepared.finish_ready setupReady (initialized_output h initialized) h.positive)
    (initMemory p (bytesAt s.mem (s.gpr .x19) 64)) (prepared.represents setupReady _ rep)).mono ?_
  intro t filled
  have bp := prepared.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)
  have sp := prepared.sp
  have work : FinalOutput.work b = FinalOutput.work a := prepared.words 248 (by decide) (by decide)
  have output : FinalOutput.output b = FinalOutput.output a := prepared.words 256 (by decide) (by decide)
  refine ⟨?_, (filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans (bp.trans initialized.bp),
    filled.sp.trans (sp.trans initialized.sp),
    filled.rd.trans (prepared.rd.trans initialized.rd), filled.wr.trans (prepared.wr.trans initialized.wr), ?_, ?_⟩
  · have digest := filled.digest
    rw [output, initializedOutput] at digest
    exact digest
  · have initialFrame := initialization_frame h initialized
    have setupFrame := setup_frame (p := p) prepared.frame
    rw [writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at setupFrame
    have fillFrame := filling_frame (by omega : 0 < p.blocks) filled.frame
    rw [writes_eq a b p bp sp prepared.matrix work output,
      writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at fillFrame
    exact (initialFrame.trans setupFrame).trans fillFrame
  · intro r hr
    have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
        r ∈ FillCompress.loopRegs ∧ r ≠ .x24 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x20 ∧ r ≠ .x21 := by decide
    obtain ⟨member, h24, h22, h23, h20, h21⟩ := facts r hr
    exact (filled.regs r member h24 h22 h23).trans
      ((prepared.regs r member h24 h20 h21 h22).trans (initialized.unused r hr))

theorem result_derive (p : Params) (password salt secret ad : List Byte) :
    result p (initialHash p password salt secret ad) = derive p password salt secret ad := by
  unfold result derive
  rw [Proof.Argon2.iterations_fill]

end VG.Proof.Argon2.AArch64.InitFill

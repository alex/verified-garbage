import VerifiedGarbage.Impl.Argon2.X86_64.FillBlock
import VerifiedGarbage.Proof.Argon2.X86_64.FillBlockFrame
import VerifiedGarbage.Proof.Argon2.X86_64.FillCacheInvariant
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelSpec

/-! Complete active filling cell against the reviewed matrix transition. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  ready : ∃ old, RandomSource.Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem code_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillBlock.code s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.FillBlock.code
  refine WP.seq ((RandomSource.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a source
  obtain ⟨counter, ready⟩ := source.ready
  have baseA : FillKernel.matrix a = FillKernel.matrix s := source.frame_word h 232 (by decide) (by decide)
  have workA : AddressCalls.work a = AddressCalls.work s := source.frame_word h 248 (by decide) (by decide)
  refine (FillKernel.code_spec_ok a p pass lane slice index ready.filling state source.represented source.random).mono ?_
  rintro t ⟨done, matrix⟩
  have baseT : FillKernel.matrix t = FillKernel.matrix a := done.frame_word ready.filling 232 (by decide) (by decide)
  have workT : AddressCalls.work t = AddressCalls.work a := done.frame_word ready.filling 248 (by decide) (by decide)
  refine ⟨⟨counter, ready.after_fill done⟩, ?_, baseT.trans baseA, workT.trans workA, ?_,
    done.rd.trans source.rd, done.wr.trans source.wr, ?_, done.mxcsr.trans source.mxcsr⟩
  · rw [baseT]; exact matrix
  · intro r hr; exact (done.regs r hr).trans (source.regs r hr)
  · have frame := kernel_frame ready.filling done
    rw [writes, baseA, workA, source.regs .rsp (by simp [calleeSaved]),
      source.regs .rbp (by simp [calleeSaved])] at frame
    exact (source_frame source).trans frame

end VG.Proof.Argon2.X86_64.FillBlock

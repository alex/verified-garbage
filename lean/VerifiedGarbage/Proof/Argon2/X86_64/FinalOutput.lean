import VerifiedGarbage.Proof.Argon2.X86_64.FinalOutputReady
import VerifiedGarbage.Proof.Argon2.Serialization

/-! The generic H′ call produces exactly the reviewed final Argon2 tag. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (output s) p.tagLen = finish p memory
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨output s, p.tagLen⟩, ⟨work s, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (block : blockAt s.mem (ReductionState.matrix s) = Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) :
    WP isa (Impl.Argon2.X86_64.FinalOutput.code name (HPrime.hash v)) s (Done s · p memory) := by
  unfold Impl.Argon2.X86_64.FinalOutput.code
  refine WP.seq ((args_ok s h.reads).mono ?_)
  intro a args
  have length := args.outputLength.trans h.tagWord
  refine (FinalCall.hPrime_call_ok v name p.tagLen a (args.ready h) args.inputLength length).mono ?_
  intro t called
  refine ⟨?_, fun r hr => (called.regs r hr).trans (args.regs r hr), called.rd.trans args.keeps.rd,
    called.wr.trans args.keeps.wr, ?_⟩
  · have input : bytesAt a.mem (a.gpr .rdi) 1024 =
        serialize (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) := by
      rw [args.keeps.mem, args.input, ← Proof.Argon2.serialize_blockAt, block]
    rw [Proof.Argon2.finish_reduction]
    have digest := called.digest
    rw [args.output, input] at digest
    exact digest
  · have frame := called.frame
    rw [args.output, args.work, args.regs .rsp (by simp [calleeSaved]), args.keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.X86_64.FinalOutput

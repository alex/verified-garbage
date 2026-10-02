import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsStage
import VerifiedGarbage.Proof.Argon2.AddressInput

/-! Both compression calls produce exactly the reviewed independent-address block. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

def writes (s : State) : List Region := [⟨work s, 8192⟩, below (s.gpr .rsp) 8]

structure Generated (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  block : blockAt t.mem (off (work s) 6144) = addressBlock p pass lane slice counter
  ready : Ready t
  work : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem

theorem stage_frame_full {s t : State} {out : Nat} (bound : out + 1024 ≤ 8192)
    (hf : Frame (stageWrites s out) s.mem t.mem) : Frame (writes s) s.mem t.mem := by
  apply hf.sub
  intro r hr
  simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨work s, 8192⟩, by simp [writes], Offset.sub_base _ bound⟩
  · exact ⟨⟨work s, 8192⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩

theorem zero_preserved {s t : State} (h : Ready s)
    (hf : Frame (stageWrites s 4096) s.mem t.mem) :
    blockAt t.mem (off (work s) 7168) = blockAt s.mem (off (work s) 7168) := by
  apply FillCompress.block_frame hf
  intro r hr
  simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (h.stackWork.sub_right (Offset.sub_base _ (by decide))).symm

theorem calls_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (zero : blockAt s.mem (off (work s) 7168) = zeroBlock)
    (input : blockAt s.mem (off (work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s (Generated s · p pass lane slice counter) := by
  unfold calls
  refine WP.seq ((stage_ok s h 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_)
  intro a first
  refine (stage_ok a first.ready 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_
  intro t second
  refine ⟨?_, second.ready, second.work.trans first.work,
    fun r hr => (second.regs r hr).trans (first.regs r hr),
    second.rd.trans first.rd, second.wr.trans first.wr, ?_⟩
  · have result := second.result
    rw [first.work, zero_preserved h first.frame, zero, first.result, zero, input] at result
    rw [Proof.Argon2.addressBlock_eq]
    exact result
  · have next := stage_frame_full (by decide) second.frame
    simp only [writes, first.work, first.regs .rsp (by simp [calleeSaved])] at next
    exact (stage_frame_full (by decide) first.frame).trans next

end VG.Proof.Argon2.X86_64.AddressCalls

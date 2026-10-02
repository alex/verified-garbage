import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsLayout
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressSetup

/-! One verified G call within the independent-address scratch layout. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

def stageWrites (s : State) (out : Nat) : List Region :=
  [⟨off (work s) out, 1024⟩, ⟨work s, 4096⟩, below s.sp 8]

structure StageDone (s t : State) (x y out : Nat) : Prop where
  result : blockAt t.mem (off (work s) out) = Spec.Argon2.compress
    (blockAt s.mem (off (work s) x)) (blockAt s.mem (off (work s) y))
  ready : Ready t
  work : work t = work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (stageWrites s out) s.mem t.mem

theorem Args.callee {s a : State} {x y out : Nat} (h : Args s a x y out)
    (r : Reg) (hr : r ∈ FillCompress.loopRegs) : a.gpr r = s.gpr r := by
  apply h.keeps.regs
  simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ready_of_frame {s t : State} (h : Ready s) (out : Nat) (ho : out + 1024 ≤ 8192)
    (regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (frame : Frame (stageWrites s out) s.mem t.mem) : Ready t ∧ work t = work s := by
  have bp := regs .x19 (by simp [FillCompress.loopRegs])
  have safe : ∀ r ∈ stageWrites s out, (⟨s.gpr .x19, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.frameWork.sub_right (Offset.sub_base _ ho)
    · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
    · exact h.frameStack
  have read : t.mem.readW (off (s.gpr .x19) 248) 64 = s.mem.readW (off (s.gpr .x19) 248) 64 :=
    frame.readW (r := ⟨s.gpr .x19, 272⟩)
      (Offset.contains_base _ (by decide) (by decide)) safe (by decide)
  have work' : work t = work s := by unfold work; rw [bp, read]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work'⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem stage_ok (s : State) (h : Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192) :
    WP isa (stage x y out) s (StageDone s · x y out) := by
  unfold stage
  refine WP.seq ((args_nat_ok s h x y out (by omega) (by omega) (by omega)).mono ?_)
  intro a args
  have callReady := args_call_ready s a h x y out hx hy ho bx by_ bo args
  refine (FillCompress.call_ok _ a callReady).mono ?_
  intro t called
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r :=
    fun r hr => (called.regs r hr).trans (args.callee r hr)
  have rd := called.rd.trans args.keeps.rd
  have wr := called.wr.trans args.keeps.wr
  have sp := called.sp.trans args.keeps.sp
  have frame : Frame (stageWrites s out) s.mem t.mem := by
    have hf := called.frame
    rw [args.output, args.scratch, args.keeps.sp, args.keeps.mem] at hf
    exact hf
  obtain ⟨ready, work'⟩ := ready_of_frame h out bo regs rd wr sp frame
  refine ⟨?_, ready, work', regs, rd, wr, sp, frame⟩
  have result := called.result
  rw [args.output, args.left, args.right, args.keeps.mem] at result
  exact result

end VG.Proof.Argon2.AArch64.AddressCalls

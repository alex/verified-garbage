import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressSetup
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
import VerifiedGarbage.Impl.Argon2.AArch64.AddressCalls
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.AArch64.Memory

/-! Merged from `Proof.Argon2.AArch64.AddressCallsLayout`. -/
section
/-! Merged from `Proof.Argon2.AArch64.AddressCallsArgs`. -/
section
/-! Independent-address compression arguments from one fixed frame read. -/
namespace VG.Proof.Argon2.AArch64.AddressCalls
open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls
open VG.Impl.Argon2.AArch64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

theorem pointer_ok (s : State) (offset : Nat) (bound : offset ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (pointer offset)) s fun t =>
      t.gpr .x0 = work s + BitVec.ofNat 64 offset ∧ Divide.Keeps [.x0, .x12, .x15] s t := by
  simp only [pointer, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x0 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, keeps⟩
  refine (Instructions.addi_ok a .x0 offset (by omega) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨out.trans (congrArg (· + BitVec.ofNat 64 offset) value), ?_⟩
  exact (keeps.mono (by simp)).trans kt

theorem args_ok (s : State) (x y out : Nat) (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (args x y out)) s fun t =>
      t.gpr .x3 = work s ∧ t.gpr .x0 = work s + BitVec.ofNat 64 x ∧
      t.gpr .x1 = work s + BitVec.ofNat 64 y ∧ t.gpr .x2 = work s + BitVec.ofNat 64 out ∧
      Divide.Keeps [.x3, .x0, .x1, .x2, .x12, .x15] s t := by
  simp only [args, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x3 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨scratch, ka⟩
  rw [← List.append_assoc (Instructions.mov .x0 .x3) (Instructions.addi .x0 x)]
  apply WP.block_append
  refine (Instructions.pointer_ok a .x0 .x3 x (by omega) (by decide) (by decide)).mono ?_
  rintro b ⟨left, kb⟩
  rw [← List.append_assoc (Instructions.mov .x1 .x3) (Instructions.addi .x1 y)]
  apply WP.block_append
  refine (Instructions.pointer_ok b .x1 .x3 y (by omega) (by decide) (by decide)).mono ?_
  rintro c ⟨right, kc⟩
  refine (Instructions.pointer_ok c .x2 .x3 out (by omega) (by decide) (by decide)).mono ?_
  rintro t ⟨output, kt⟩
  have scrB := kb.regs .x3 (by decide)
  have scrC := kc.regs .x3 (by decide)
  refine ⟨(kt.regs .x3 (by decide)).trans (scrC.trans (scrB.trans scratch)),
    (kt.regs .x0 (by decide)).trans ((kc.regs .x0 (by decide)).trans
      (left.trans (congrArg (· + BitVec.ofNat 64 x) scratch))),
    (kt.regs .x1 (by decide)).trans (right.trans (congrArg (· + BitVec.ofNat 64 y) (scrB.trans scratch))),
    output.trans (congrArg (· + BitVec.ofNat 64 out) (scrC.trans (scrB.trans scratch))), ?_⟩
  exact (ka.mono (by decide)).trans ((kb.mono (by decide)).trans
    ((kc.mono (by decide)).trans (kt.mono (by decide))))
end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Permissions and separation for either address-generation compression call. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64

structure Ready (s : State) : Prop where
  frameRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8
  workWrite : Covers [⟨work s, 8192⟩] s.wr
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨work s, 8192⟩
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)
  stackWork : (below s.sp 8).Disjoint ⟨work s, 8192⟩

theorem work_cover (s : State) (h : Ready s) (d n : Nat) (hd : d + n ≤ 8192) :
    Covers [⟨off (work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (work s) d, n⟩] [⟨work s, 8192⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨work s, 8192⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

structure Args (s a : State) (x y out : Nat) : Prop where
  scratch : a.gpr .x3 = work s
  left : a.gpr .x0 = off (work s) x
  right : a.gpr .x1 = off (work s) y
  output : a.gpr .x2 = off (work s) out
  keeps : Divide.Keeps [.x3, .x0, .x1, .x2, .x12, .x15] s a

theorem args_nat_ok (s : State) (h : Ready s) (x y out : Nat)
    (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192) :
    WP isa (.block (Impl.Argon2.AArch64.AddressCalls.args x y out)) s (Args s · x y out) := by
  refine (args_ok s x y out hx hy ho h.frameRead).mono ?_
  rintro a ⟨scratch, left, right, output, keeps⟩
  exact ⟨scratch, left, right, output, keeps⟩

theorem args_call_ready (s a : State) (h : Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (args : Args s a x y out) : FillCompress.CallReady a := by
  have read (d : Nat) (hd : d + 1024 ≤ 8192) :
      Covers [⟨off (work s) d, 1024⟩] (a.rd ++ a.wr) := by
    rw [args.keeps.rd, args.keeps.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := work_cover s h d 1024 hd p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have sp : a.sp = s.sp := args.keeps.sp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [args.left]; exact read x bx
  · rw [args.right]; exact read y by_
  · rw [args.output, args.keeps.wr]; exact work_cover s h out 1024 bo
  · rw [args.scratch, args.keeps.wr]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using work_cover s h 0 4096 (by decide)
  · rw [args.left, args.scratch]; exact Offset.disjoint_base _ hx (by omega)
  · rw [args.right, args.scratch]; exact Offset.disjoint_base _ hy (by omega)
  · rw [args.output, args.scratch]; exact Offset.disjoint_base _ ho (by omega)
  · rw [sp, args.left]; exact h.stackWork.sub_right (Offset.sub_base _ bx)
  · rw [sp, args.right]; exact h.stackWork.sub_right (Offset.sub_base _ by_)
  · rw [sp, args.output]; exact h.stackWork.sub_right (Offset.sub_base _ bo)
  · rw [sp, args.scratch]; exact h.stackWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.AArch64.AddressCalls
end

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

import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall
import VerifiedGarbage.Impl.Argon2.X86_64.AddressCalls
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords

/-! Merged from `Proof.Argon2.X86_64.AddressCallsLayout`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressCallsArgs`. -/
section
/-! Independent-address compression arguments from one fixed frame read. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def displacement (n : Nat) : Addr := BitVec.signExtend 64 (BitVec.ofNat 32 n)

theorem pointer_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block (pointer offset)) s fun t =>
      t.gpr .rdi = work s + displacement offset ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [pointer, work, displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, ite_true, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem args_ok (s : State) (x y out : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block (args x y out)) s fun t =>
      t.gpr .rcx = work s ∧ t.gpr .rdi = work s + displacement x ∧
      t.gpr .rsi = work s + displacement y ∧ t.gpr .rdx = work s + displacement out ∧
      Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s t := by
  apply WP.of_runBlock
  simp only [args, work, displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Permissions and separation for either address-generation compression call. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64

structure Ready (s : State) : Prop where
  frameRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8
  workWrite : Covers [⟨work s, 8192⟩] s.wr
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 8192⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 8192⟩

theorem displacement_eq (n : Nat) (bound : n ≤ 8192) : displacement n = BitVec.ofNat 64 n := by
  have n32 : n < 2 ^ 32 := by omega
  have msb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n32]
    omega
  unfold displacement
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb,
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) n32]

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
  scratch : a.gpr .rcx = work s
  left : a.gpr .rdi = off (work s) x
  right : a.gpr .rsi = off (work s) y
  output : a.gpr .rdx = off (work s) out
  keeps : Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s a

theorem args_nat_ok (s : State) (h : Ready s) (x y out : Nat)
    (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192) :
    WP isa (.block (Impl.Argon2.X86_64.AddressCalls.args x y out)) s (Args s · x y out) := by
  refine (args_ok s x y out h.frameRead).mono ?_
  rintro a ⟨scratch, left, right, output, keeps⟩
  rw [displacement_eq x hx] at left
  rw [displacement_eq y hy] at right
  rw [displacement_eq out ho] at output
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
  have sp : a.gpr .rsp = s.gpr .rsp := args.keeps.regs .rsp (by decide)
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

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! One verified G call within the independent-address scratch layout. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

def stageWrites (s : State) (out : Nat) : List Region :=
  [⟨off (work s) out, 1024⟩, ⟨work s, 4096⟩, below (s.gpr .rsp) 8]

structure StageDone (s t : State) (x y out : Nat) : Prop where
  result : blockAt t.mem (off (work s) out) = Spec.Argon2.compress
    (blockAt s.mem (off (work s) x)) (blockAt s.mem (off (work s) y))
  ready : Ready t
  work : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (stageWrites s out) s.mem t.mem

theorem Args.callee {s a : State} {x y out : Nat} (h : Args s a x y out)
    (r : Reg) (hr : r ∈ calleeSaved) : a.gpr r = s.gpr r := by
  apply h.keeps.regs
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ready_of_frame {s t : State} (h : Ready s) (out : Nat) (ho : out + 1024 ≤ 8192)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame (stageWrites s out) s.mem t.mem) : Ready t ∧ work t = work s := by
  have bp := regs .rbp (by simp [calleeSaved])
  have sp := regs .rsp (by simp [calleeSaved])
  have safe : ∀ r ∈ stageWrites s out, (⟨s.gpr .rbp, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.frameWork.sub_right (Offset.sub_base _ ho)
    · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
    · exact h.frameStack
  have read : t.mem.readW (off (s.gpr .rbp) 248) 64 = s.mem.readW (off (s.gpr .rbp) 248) 64 :=
    frame.readW (r := ⟨s.gpr .rbp, 272⟩)
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
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r :=
    fun r hr => (called.regs r hr).trans (args.callee r hr)
  have rd := called.rd.trans args.keeps.rd
  have wr := called.wr.trans args.keeps.wr
  have frame : Frame (stageWrites s out) s.mem t.mem := by
    have hf := called.frame
    rw [args.output, args.scratch, args.callee .rsp (by simp [calleeSaved]), args.keeps.mem] at hf
    exact hf
  obtain ⟨ready, work'⟩ := ready_of_frame h out bo regs rd wr frame
  refine ⟨?_, ready, work', regs, rd, wr, frame⟩
  have result := called.result
  rw [args.output, args.left, args.right, args.keeps.mem] at result
  exact result

end VG.Proof.Argon2.X86_64.AddressCalls

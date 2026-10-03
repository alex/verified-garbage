import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
import VerifiedGarbage.Proof.Argon2.AArch64.FillWriteCover
import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.Memory

/-! Merged from `Proof.Argon2.AArch64.FillCompressArgs`. -/
section
/-! Save the current cell across G and reload the block-write arguments. -/
namespace VG.Proof.Argon2.AArch64.FillCompress
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress
open VG.Impl.Argon2.AArch64

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .x19) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [saveCurrent, Instructions.store, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.store, State.read, Size.bytes, and_self, Option.bind_some, Size.bits, BitVec.setWidth_eq, hw,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 248) 64 ∧
      t.gpr .x2 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧ Divide.Keeps [.x3, .x2, .x12, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [compressArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    hr,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 16) 64 ∧
      t.gpr .x1 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧
      t.gpr .x5 = s.mem.readW (off (s.gpr .x19) 0) 64 ∧ Divide.Keeps [.x0, .x1, .x5, .x12, .x15] s t := by
  simp only [off, BitVec.add_zero] at destRead workRead passRead
  apply WP.of_runBlock
  simp only [writeArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, Size.bits, BitVec.setWidth_eq,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, BitVec.add_zero,
    destRead, workRead, passRead,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.FillCompress
end

/-! Compression followed by first/later-pass writing, preserving the frame
slots and the old destination cell across the compression call. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def callWrites (s : State) : List Region :=
  [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩, below s.sp 8]

def destination (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 16) 64

def pass (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 0) 64

structure OperationReady (s : State) : Prop where
  call : CallReady s
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  workWord : s.mem.readW (off (s.gpr .x19) 248) 64 = s.gpr .x3
  outputPointer : s.gpr .x3 + 4096 = s.gpr .x2
  destinationWrite : Covers [⟨destination s, 1024⟩] s.wr
  frameSafe : ∀ r ∈ callWrites s, (⟨s.gpr .x19, 272⟩ : Region).Disjoint r
  destinationSafe : ∀ r ∈ callWrites s, (⟨destination s, 1024⟩ : Region).Disjoint r

structure OperationDone (s t : State) : Prop where
  block : blockAt t.mem (destination s) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
    if pass s = 0 then next else xorBlock next (blockAt s.mem (destination s))
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (⟨destination s, 1024⟩ :: callWrites s) s.mem t.mem

theorem frame_word {s t : State} (h : OperationReady s) (called : Called s t)
    (d : Nat) (hd : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 :=
  called.frame.readW (r := ⟨s.gpr .x19, 272⟩)
    (Offset.contains_base _ hd (by omega)) h.frameSafe (by decide)

theorem destination_unchanged {s t : State} (h : OperationReady s) (called : Called s t) :
    blockAt t.mem (destination s) = blockAt s.mem (destination s) := by
  apply Vector.ext
  intro i hi
  have read : t.mem.readW (off (destination s) (8 * i)) 64 =
      s.mem.readW (off (destination s) (8 * i)) 64 :=
    called.frame.readW (r := ⟨destination s, 1024⟩)
      (Offset.contains_base _ (by omega) (by omega)) h.destinationSafe (by decide)
  rw [← blockAt_get t.mem (destination s) ⟨i, hi⟩,
    ← blockAt_get s.mem (destination s) ⟨i, hi⟩] at read
  exact read

theorem operation_ok (s : State) (h : OperationReady s) :
    WP isa operation s (OperationDone s) := by
  unfold operation
  refine WP.seq ((call_ok _ s h.call).mono ?_)
  intro a called
  have bp : a.gpr .x19 = s.gpr .x19 := called.regs .x19 (by simp [loopRegs])
  have reads (d : Nat) (hd : d ∈ [0, 16, 248]) :
      InRegions (a.rd ++ a.wr) (off (a.gpr .x19) d) 8 := by
    rw [called.rd, called.wr, bp]; exact h.frameRead d hd
  refine WP.seq ((writeArgs_ok a (reads 16 (by simp)) (reads 248 (by simp))
    (reads 0 (by simp))).mono ?_)
  rintro b ⟨dest, src, counter, keeps⟩
  have dest' : b.gpr .x0 = destination s := by
    rw [dest, bp, frame_word h called 16 (by decide), destination]
  have src' : b.gpr .x1 = s.gpr .x2 := by
    rw [src, bp, frame_word h called 248 (by decide), h.workWord, h.outputPointer]
  have counter' : b.gpr .x5 = pass s := by
    rw [counter, bp, frame_word h called 0 (by decide), pass]
  have readable : Covers [⟨b.gpr .x1, 1024⟩] (b.rd ++ b.wr) := by
    rw [src', keeps.rd, keeps.wr, called.rd, called.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := h.call.output p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writable : Covers [⟨b.gpr .x0, 1024⟩] b.wr := by
    rw [dest', keeps.wr, called.wr]; exact h.destinationWrite
  have sep : (⟨b.gpr .x1, 1024⟩ : Region).Disjoint ⟨b.gpr .x0, 1024⟩ := by
    rw [src', dest']; exact (h.destinationSafe _ (by simp [callWrites])).symm
  refine (FillWrite.code_cover_ok b readable writable sep).mono ?_
  rintro t ⟨value, frame, tk, tsp⟩
  refine ⟨?_, ?_, tk.2.1.trans (keeps.rd.trans called.rd),
    tk.2.2.trans (keeps.wr.trans called.wr), tsp.trans (keeps.sp.trans called.sp), ?_⟩
  · rw [dest', src', counter', keeps.mem, called.result, destination_unchanged h called] at value
    exact value
  · intro r hr
    have safe : r ≠ .x8 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧
        r ∉ [Reg.x0, .x1, .x5, .x12, .x15] := by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1).trans
      ((keeps.regs r safe.2.2.2.2).trans (called.regs r hr))
  · rw [dest'] at frame
    rw [keeps.mem] at frame
    exact (called.frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frame.mono (by simp))

end VG.Proof.Argon2.AArch64.FillCompress

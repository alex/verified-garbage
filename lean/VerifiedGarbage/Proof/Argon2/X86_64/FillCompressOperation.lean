import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall
import VerifiedGarbage.Proof.Argon2.X86_64.FillWriteCover
import VerifiedGarbage.Impl.Argon2.X86_64.FillCompress
import VerifiedGarbage.Proof.Argon2.X86_64.Memory
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! Merged from `Proof.Argon2.X86_64.FillCompressArgs`. -/
section
/-! Save the current cell across G and reload the block-write arguments. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .rbp) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [saveCurrent, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .rcx = s.mem.readW (off (s.gpr .rbp) 248) 64 ∧
      t.gpr .rdx = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      Divide.Keeps [.rcx, .rdx] s t := by
  apply WP.of_runBlock
  simp only [compressArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 16) 64 ∧
      t.gpr .rsi = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      t.gpr .r9 = s.mem.readW (off (s.gpr .rbp) 0) 64 ∧
      Divide.Keeps [.rdi, .rsi, .r9] s t := by
  apply WP.of_runBlock
  simp only [writeArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, ea_at, destRead, workRead, passRead, execAlu,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Compression followed by first/later-pass writing, preserving the frame
slots and the old destination cell across the compression call. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def callWrites (s : State) : List Region :=
  [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩, below (s.gpr .rsp) 8]

def destination (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 16) 64

def pass (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 0) 64

structure OperationReady (s : State) : Prop where
  call : CallReady s
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  workWord : s.mem.readW (off (s.gpr .rbp) 248) 64 = s.gpr .rcx
  outputPointer : s.gpr .rcx + 4096 = s.gpr .rdx
  destinationWrite : Covers [⟨destination s, 1024⟩] s.wr
  frameSafe : ∀ r ∈ callWrites s, (⟨s.gpr .rbp, 272⟩ : Region).Disjoint r
  destinationSafe : ∀ r ∈ callWrites s, (⟨destination s, 1024⟩ : Region).Disjoint r

structure OperationDone (s t : State) : Prop where
  block : blockAt t.mem (destination s) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    if pass s = 0 then next else xorBlock next (blockAt s.mem (destination s))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (⟨destination s, 1024⟩ :: callWrites s) s.mem t.mem

theorem frame_word {s t : State} (h : OperationReady s) (called : Called s t)
    (d : Nat) (hd : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 :=
  called.frame.readW (r := ⟨s.gpr .rbp, 272⟩)
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
  have bp : a.gpr .rbp = s.gpr .rbp := called.regs .rbp (by simp [calleeSaved])
  have reads (d : Nat) (hd : d ∈ [0, 16, 248]) :
      InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) d) 8 := by
    rw [called.rd, called.wr, bp]; exact h.frameRead d hd
  refine WP.seq ((writeArgs_ok a (reads 16 (by simp)) (reads 248 (by simp))
    (reads 0 (by simp))).mono ?_)
  rintro b ⟨dest, src, counter, keeps⟩
  have dest' : b.gpr .rdi = destination s := by
    rw [dest, bp, frame_word h called 16 (by decide), destination]
  have src' : b.gpr .rsi = s.gpr .rdx := by
    rw [src, bp, frame_word h called 248 (by decide), h.workWord, h.outputPointer]
  have counter' : b.gpr .r9 = pass s := by
    rw [counter, bp, frame_word h called 0 (by decide), pass]
  have readable : Covers [⟨b.gpr .rsi, 1024⟩] (b.rd ++ b.wr) := by
    rw [src', keeps.rd, keeps.wr, called.rd, called.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := h.call.output p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writable : Covers [⟨b.gpr .rdi, 1024⟩] b.wr := by
    rw [dest', keeps.wr, called.wr]; exact h.destinationWrite
  have sep : (⟨b.gpr .rsi, 1024⟩ : Region).Disjoint ⟨b.gpr .rdi, 1024⟩ := by
    rw [src', dest']; exact (h.destinationSafe _ (by simp [callWrites])).symm
  refine (FillWrite.code_cover_ok b readable writable sep).mono ?_
  rintro t ⟨value, frame, tk, _⟩
  refine ⟨?_, ?_, tk.2.1.trans (keeps.rd.trans called.rd),
    tk.2.2.trans (keeps.wr.trans called.wr), ?_⟩
  · rw [dest', src', counter', keeps.mem, called.result, destination_unchanged h called] at value
    exact value
  · intro r hr
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have nk : r ∉ [Reg.rdi, .rsi, .r9] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne).trans ((keeps.regs r nk).trans (called.regs r hr))
  · rw [dest'] at frame
    rw [keeps.mem] at frame
    exact (called.frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frame.mono (by simp))

end VG.Proof.Argon2.X86_64.FillCompress

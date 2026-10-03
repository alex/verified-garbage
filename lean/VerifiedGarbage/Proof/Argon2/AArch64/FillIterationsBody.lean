import VerifiedGarbage.Impl.Argon2.AArch64.FillIterations
import VerifiedGarbage.Proof.Argon2.AArch64.FillIteration

/-! Merged from `Proof.Argon2.AArch64.FillPassSave`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillPassCounter`. -/
section
/-! Increment, save and compare the public pass counter. -/
namespace VG.Proof.Argon2.AArch64.FillIterations
open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .x8 = s.mem.readW (off (s.gpr .x19) 0) 64 + 1 ∧
      Divide.Keeps [.x8, .x12, .x15] s t := by
  simp only [increment, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x8 .x19 0 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, ka⟩
  refine (Instructions.addi_ok a .x8 1 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [out, value]; rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (off (s.gpr .x19) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 72) 8)
    (ha : (s.gpr .x8).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.gpr .x8) ∧
      (∀ r, r ∉ [Reg.x13, .x14, .x15] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
        (s.mem.readW (off (s.gpr .x19) 72) 64).toNat)) := by
  simp only [saveCheck, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.store_ok s .x19 .x8 0 (by decide) (by decide) hw).mono ?_
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have unchanged : a.mem.readW (off (a.gpr .x19) 72) 64 =
      s.mem.readW (off (s.gpr .x19) 72) 64 := by
    rw [regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by rw [regs, rd, wr]; exact hr
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [regs]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by rw [unchanged]; exact hb
  refine (Instructions.comparem_ok a .x8 .x19 72 (by decide) (by decide) (by decide)
    read left right).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨keeps.mem.trans mem, ?_, keeps.rd.trans rd, keeps.wr.trans wr, keeps.sp.trans sp, ?_⟩
  · intro r hr; exact (keeps.regs r hr).trans (congrFun regs r)
  · change eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
      (s.mem.readW (off (s.gpr .x19) 72) 64).toNat))
    change eval (.nonzero .x .x14) t = some (decide ((a.gpr .x8).toNat <
      (a.mem.readW (off (a.gpr .x19) 72) 64).toNat)) at flag
    rw [flag, regs, mem]
    rw [Mem.readW_writeW_sep (w := 64) (w' := 64)
      (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! A saved pass counter changes only its eight-byte header word. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.mem.readW (off (s.gpr .x19) 0) 64 + 1)
  regs : ∀ r, r ∉ [Reg.x8, .x12, .x13, .x14, .x15] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cf : eval (.nonzero .x .x14) t = some (decide ((s.mem.readW (off (s.gpr .x19) 0) 64 + 1).toNat <
    (s.mem.readW (off (s.gpr .x19) 72) 64).toNat))
  frame : Frame [⟨off (s.gpr .x19) 0, 8⟩] s.mem t.mem

theorem advance_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (write : InRegions s.wr (off (s.gpr .x19) 0) 8)
    (passesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 72) 8)
    (ha : (s.mem.readW (off (s.gpr .x19) 0) 64 + 1).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) : WP isa advance s (Saved s) := by
  unfold advance
  refine WP.seq ((increment_ok s read).mono ?_)
  rintro a ⟨value, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have readA : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact passesRead
  have writeA : InRegions a.wr (off (a.gpr .x19) 0) 8 := by rw [keeps.wr, bp]; exact write
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [value]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [keeps.mem, bp]; exact hb
  refine (saveCheck_ok a writeA readA left right).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx, cf⟩
  have finalMem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.mem.readW (off (s.gpr .x19) 0) 64 + 1) := by
    rw [mem, keeps.mem, bp, value]
  refine ⟨finalMem, ?_, rd.trans keeps.rd, wr.trans keeps.wr, mx.trans keeps.sp, ?_, ?_⟩
  · intro r ne
    have small : r ∉ [Reg.x8, .x12, .x15] := by
      intro hr; apply ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp_all
    have compare : r ∉ [Reg.x13, .x14, .x15] := by
      intro hr; apply ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp_all
    exact (regs r compare).trans (keeps.regs r small)
  · rw [cf, value, keeps.mem, bp]
  · rw [finalMem]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 0, 8⟩) (by simp) _ (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs .x19 (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8)
    (by omega) (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s) :
    AddressHeader.Words p (pass + 1) lane slice old t := by
  refine ⟨?_, (h.regs .x24 (by decide)).trans words.laneWord,
    (h.regs .x22 (by decide)).trans words.sliceWord,
    (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord,
    (h.read 8 (by decide) (by decide)).trans words.counterWord⟩
  rw [h.regs .x19 (by decide), h.mem, Mem.readW_writeW_self64, words.passWord, BitVec.ofNat_add]
  rfl

theorem Saved.header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) : FillHeader.Ready p (pass + 1) lane slice t := by
  have bp := h.regs .x19 (by decide)
  have sp := h.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := h.read 248 (by decide) (by decide)
  refine ⟨header.layout.of_preserved bp sp base work h.rd h.wr, ?_, ?_, ?_, ?_, ?_,
    (h.regs .x20 (by decide)).trans header.laneLength, (h.regs .x21 (by decide)).trans header.segmentLength, ?_⟩
  · constructor
    · rw [h.rd, h.wr, bp]; exact header.addressLayout.frameRead
    · rw [h.wr, work]; exact header.addressLayout.workWrite
    · rw [bp, work]; exact header.addressLayout.frameWork
    · rw [bp, sp]; exact header.addressLayout.frameStack
    · rw [sp, work]; exact header.addressLayout.stackWork
  · rw [h.rd, h.wr, bp]; exact header.reads
  · rw [h.wr, bp]; exact header.write
  · obtain ⟨old, words⟩ := header.words; exact ⟨old, h.words words⟩
  · rw [base, work]; exact header.matrixWork
  · exact (h.read 184 (by decide) (by decide)).trans header.lanesWord

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! Merged from `Proof.Argon2.AArch64.FillIterationsFrame`. -/
section
/-! The outer pass loop also writes the public pass word at frame offset zero. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.sp) 8, ⟨s.gpr .x19, 24⟩]

theorem filling_frame {s t : State} {p : Params} (h : Frame (FillBlock.writes s p) s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillBlock.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x19, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.outer_frame {s t : State} {p : Params} (h : Saved s t) : Frame (writes s p) s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .x19, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.represents {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  rw [base]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (header.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! A complete pass retains the matrix and advances its public iteration counter. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  filling : FillIteration.Ready p pass s
  passesBound : p.passes < 2 ^ 32
  passWrite : InRegions s.wr (off (s.gpr .x19) 0) 8

structure Done (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks (fillPass p state pass).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p (pass + 1) p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (pass + 1 < p.passes))
  next : pass + 1 < p.passes → Ready p (pass + 1) t

theorem body_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIterations.body s (Done s · p pass state) := by
  unfold Impl.Argon2.AArch64.FillIterations.body
  refine WP.seq ((FillIteration.code_ok s p pass h.filling state represented).mono ?_)
  intro a filled
  have write : InRegions a.wr (off (a.gpr .x19) 0) 8 := by
    rw [filled.wr, filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)]
    exact h.passWrite
  obtain ⟨old, words⟩ := filled.header.words
  have passBound := h.filling.parameters.passBound
  have added : (BitVec.ofNat 64 pass + 1 : Addr) = BitVec.ofNat 64 (pass + 1) := by
    rw [BitVec.ofNat_add]; rfl
  have left : (a.mem.readW (off (a.gpr .x19) 0) 64 + 1).toNat < 2 ^ 63 := by
    rw [words.passWord, added, ReferenceMap.word_nat (pass + 1) (by omega)]; omega
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [words.passesWord, ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
    exact Nat.lt_trans h.passesBound (by decide)
  refine (advance_ok a (filled.header.reads 0 (by simp)) write
    (filled.header.reads 72 (by simp)) left right).mono ?_
  intro t saved
  have header := saved.header filled.header
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.sp.trans filled.sp, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [writes, filled.matrix, filled.work,
      filled.sp,
      filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at lastFrame
    exact (filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x8, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .x19 (by decide)]; exact write

end VG.Proof.Argon2.AArch64.FillIterations

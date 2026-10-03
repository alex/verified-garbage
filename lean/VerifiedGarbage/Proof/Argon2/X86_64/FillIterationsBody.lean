import VerifiedGarbage.Impl.Argon2.X86_64.FillIterations
import VerifiedGarbage.Proof.Argon2.X86_64.FillIteration

/-! Merged from `Proof.Argon2.X86_64.FillPassSave`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillPassCounter`. -/
section
/-! Increment, save and compare the public pass counter. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .rax = s.mem.readW (off (s.gpr .rbp) 0) 64 + 1 ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [increment, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (off (s.gpr .rbp) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 72) 8) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      t.cf = decide ((s.gpr .rax).toNat < (s.mem.readW (off (s.gpr .rbp) 72) 64).toNat) := by
  apply WP.of_runBlock
  have sep : Mem.Sep (off (s.gpr .rbp) 72) 8 (off (s.gpr .rbp) 0) 8 :=
    Offset.sep _ (by decide) (by decide) (by decide)
  simp only [saveCheck, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.load64, ea_at, hw, hr, readSrc, execAlu, ite_true,
    Mem.readW_writeW_sep (w := 64) (w' := 64) sep (by decide), RegUpd.cf_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, trivial⟩
  rfl

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! A saved pass counter changes only its eight-byte header word. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (s.mem.readW (off (s.gpr .rbp) 0) 64 + 1)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  cf : t.cf = decide ((s.mem.readW (off (s.gpr .rbp) 0) 64 + 1).toNat <
    (s.mem.readW (off (s.gpr .rbp) 72) 64).toNat)
  frame : Frame [⟨off (s.gpr .rbp) 0, 8⟩] s.mem t.mem

theorem advance_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (write : InRegions s.wr (off (s.gpr .rbp) 0) 8)
    (passesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 72) 8) : WP isa advance s (Saved s) := by
  unfold advance
  refine WP.seq ((increment_ok s read).mono ?_)
  rintro a ⟨value, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have readA : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 72) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact passesRead
  have writeA : InRegions a.wr (off (a.gpr .rbp) 0) 8 := by rw [keeps.wr, bp]; exact write
  refine (saveCheck_ok a writeA readA).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx, cf⟩
  have finalMem : t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (s.mem.readW (off (s.gpr .rbp) 0) 64 + 1) := by
    rw [mem, keeps.mem, bp, value]
  refine ⟨finalMem, ?_, rd.trans keeps.rd, wr.trans keeps.wr, mx.trans keeps.mxcsr, ?_, ?_⟩
  · intro r ne
    have outside : r ∉ [Reg.rax] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne
    exact (congrFun regs r).trans (keeps.regs r outside)
  · rw [cf, value, keeps.mem, bp]
  · rw [finalMem]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 0, 8⟩) (by simp) _ (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs .rbp (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8)
    (by omega) (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s) :
    AddressHeader.Words p (pass + 1) lane slice old t := by
  refine ⟨?_, (h.regs .rbx (by decide)).trans words.laneWord,
    (h.regs .r14 (by decide)).trans words.sliceWord,
    (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord,
    (h.read 8 (by decide) (by decide)).trans words.counterWord⟩
  rw [h.regs .rbp (by decide), h.mem, Mem.readW_writeW_self64, words.passWord, BitVec.ofNat_add]
  rfl

theorem Saved.header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : Saved s t) (header : FillHeader.Ready p pass lane slice s) : FillHeader.Ready p (pass + 1) lane slice t := by
  have bp := h.regs .rbp (by decide)
  have sp := h.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := h.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := h.read 248 (by decide) (by decide)
  refine ⟨header.layout.of_preserved bp sp base work h.rd h.wr, ?_, ?_, ?_, ?_, ?_,
    (h.regs .r12 (by decide)).trans header.laneLength, (h.regs .r13 (by decide)).trans header.segmentLength, ?_⟩
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

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! Merged from `Proof.Argon2.X86_64.FillIterationsFrame`. -/
section
/-! The outer pass loop also writes the public pass word at frame offset zero. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.gpr .rsp) 8, ⟨s.gpr .rbp, 24⟩]

theorem filling_frame {s t : State} {p : Params} (h : Frame (FillBlock.writes s p) s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillBlock.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .rbp, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem Saved.outer_frame {s t : State} {p : Params} (h : Saved s t) : Frame (writes s p) s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .rbp, 24⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

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

end VG.Proof.Argon2.X86_64.FillIterations
end

/-! A complete pass retains the matrix and advances its public iteration counter. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  filling : FillIteration.Ready p pass s
  passesBound : p.passes < 2 ^ 32
  passWrite : InRegions s.wr (off (s.gpr .rbp) 0) 8

structure Done (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks (fillPass p state pass).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p (pass + 1) p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  cf : t.cf = decide (pass + 1 < p.passes)
  next : pass + 1 < p.passes → Ready p (pass + 1) t

theorem body_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillIterations.body s (Done s · p pass state) := by
  unfold Impl.Argon2.X86_64.FillIterations.body
  refine WP.seq ((FillIteration.code_ok s p pass h.filling state represented).mono ?_)
  intro a filled
  have write : InRegions a.wr (off (a.gpr .rbp) 0) 8 := by
    rw [filled.wr, filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)]
    exact h.passWrite
  refine (advance_ok a (filled.header.reads 0 (by simp)) write (filled.header.reads 72 (by simp))).mono ?_
  intro t saved
  have header := saved.header filled.header
  obtain ⟨old, words⟩ := filled.header.words
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  have passBound := h.filling.parameters.passBound
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.mxcsr.trans filled.mxcsr, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [writes, filled.matrix, filled.work,
      filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at lastFrame
    exact (filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · have added : (BitVec.ofNat 64 pass + 1 : Addr) = BitVec.ofNat 64 (pass + 1) := by
      rw [BitVec.ofNat_add]; rfl
    rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .rbp (by decide)]; exact write

end VG.Proof.Argon2.X86_64.FillIterations

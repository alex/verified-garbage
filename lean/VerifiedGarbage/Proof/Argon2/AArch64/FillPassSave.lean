import VerifiedGarbage.Proof.Argon2.AArch64.FillPassCounter

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

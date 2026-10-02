import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheMeta

/-! Save the public cache counter without disturbing scratch or header fields. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

theorem save_ok (s : State) (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) :
    WP isa (.block save) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  ready : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem

theorem save_ready (s : State) (h : AddressCalls.Ready s)
    (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) : WP isa (.block save) s (Saved s) := by
  refine (save_ok s hw).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx⟩
  have work' : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work
    rw [regs, mem, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
  have ready : AddressCalls.Ready t := by
    constructor
    · rw [rd, wr, regs]; exact h.frameRead
    · rw [work', wr]; exact h.workWrite
    · rw [regs, work']; exact h.frameWork
    · rw [regs]; exact h.frameStack
    · rw [regs, work']; exact h.stackWork
  refine ⟨mem, regs, rd, wr, mx, ready, work', ?_⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 8, 8⟩) (by simp) _
    (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat)
    (hd : d + 8 ≤ 8 ∨ 16 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ hd (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old counter : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s)
    (value : s.gpr .rax = BitVec.ofNat 64 counter) :
    AddressHeader.Words p pass lane slice counter t := by
  refine ⟨(h.read 0 (by decide) (by decide)).trans words.passWord,
    ?_, ?_, (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord, ?_⟩
  · rw [h.regs]; exact words.laneWord
  · rw [h.regs]; exact words.sliceWord
  · rw [h.regs, h.mem, Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.X86_64.AddressCache

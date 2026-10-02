import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelLayout
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMap

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    WP isa (.block [.mov r (.mem (Impl.Argon2.X86_64.at_ .rbp d))]) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .rbp) d) 64 ∧ Divide.Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, read, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ite_eq_right hq
  all_goals rfl

structure Ready (p : Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1
  column : t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.mapping s (Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.mapping
  refine WP.seq ((load_ok s .rsi 184 (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .rdi (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .r10 = FillPointers.cell (matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .rdi = FillPointers.cell (matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .rsi = FillPointers.cell (matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : Params) (pass lane slice index refLane refColumn : Nat)
    (layout : Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .r9 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .rdi = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.X86_64.FillKernel.pointers s (Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.X86_64.FillKernel.pointers
  refine WP.seq ((load_ok s .r8 232 (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .r9 = BitVec.ofNat 64 refLane := (keeps.regs .r9 (by decide)).trans laneWord
  have col' : a.gpr .rdi = BitVec.ofNat 64 refColumn := (keeps.regs .rdi (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.X86_64.FillKernel

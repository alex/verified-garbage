import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelLayout
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMap
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat) (ha : d % 8 = 0) (hb : d < 32768)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.load r .x19 d].flatten) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .x19) d) 64 ∧ Divide.Keeps [r] s t := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    Instructions.load_ok s r .x19 d ha hb read

structure Ready (p : Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).1
  column : t.gpr .x0 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).2
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.mapping s (Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.mapping Impl.Argon2.AArch64.FillKernel.lanes
  refine WP.seq ((load_ok s .x1 184 (by decide) (by decide) (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .x0 (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .x6 = FillPointers.cell (matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .x0 = FillPointers.cell (matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .x1 = FillPointers.cell (matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : Params) (pass lane slice index refLane refColumn : Nat)
    (layout : Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .x5 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.AArch64.FillKernel.pointers s (Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.AArch64.FillKernel.pointers Impl.Argon2.AArch64.FillKernel.matrix
  refine WP.seq ((load_ok s .x4 232 (by decide) (by decide) (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .x5 = BitVec.ofNat 64 refLane := (keeps.regs .x5 (by decide)).trans laneWord
  have col' : a.gpr .x0 = BitVec.ofNat 64 refColumn := (keeps.regs .x0 (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.AArch64.FillKernel

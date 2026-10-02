import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersNat
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress
import VerifiedGarbage.Impl.Argon2.X86_64.FillKernel

/-! One allocation invariant covers all matrix cells used by the filling step. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 232) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

structure Layout (p : Params) (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 184, 232, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .rbp) 16) 8
  matrixWrite : Covers [⟨matrix s, p.blocks * 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  matrixWork : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  matrixFrame : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  matrixStack : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 5120⟩

theorem Layout.of_keeps {p : Params} {s t : State} (h : Layout p s)
    (k : Divide.Keeps ReferenceMap.changed s t) : Layout p t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
  have matrix' : matrix t = matrix s := by unfold matrix; rw [bp, k.mem]
  have work' : work t = work s := by unfold work; rw [bp, k.mem]
  constructor
  · rw [k.rd, k.wr, bp]; exact h.frameRead
  · rw [k.wr, bp]; exact h.frameWrite
  · rw [matrix', k.wr]; exact h.matrixWrite
  · rw [work', k.wr]; exact h.workWrite
  · rw [matrix', work']; exact h.matrixWork
  · rw [matrix', bp]; exact h.matrixFrame
  · rw [matrix', sp]; exact h.matrixStack
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem cell_sub (p : Params) (base : Addr) (positive : 0 < p.lanes) {lane column : Nat}
    (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Region.Sub ⟨FillPointers.cell base p lane column, 1024⟩ ⟨base, p.blocks * 1024⟩ :=
  Offset.sub_base base (Proof.Argon2.cell_bytes p positive hl hc)

theorem Layout.cell_cover {p : Params} {s : State} (h : Layout p s) (positive : 0 < p.lanes)
    {lane column : Nat} (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩] s.wr := by
  have sub : Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩]
      [⟨matrix s, p.blocks * 1024⟩] := Covers.of_sub (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨⟨matrix s, p.blocks * 1024⟩, by simp, (lane * p.laneLen + column) * 1024,
          rfl, Proof.Argon2.cell_bytes p positive hl hc⟩)
  exact fun a n ha => h.matrixWrite a n (sub a n ha)

theorem compress_ready (p : Params) (s : State) (layout : Layout p s)
    (positive : 0 < p.lanes) (leftLane leftColumn rightLane rightColumn destLane destColumn : Nat)
    (ll : leftLane < p.lanes) (lc : leftColumn < p.laneLen)
    (rl : rightLane < p.lanes) (rc : rightColumn < p.laneLen)
    (dl : destLane < p.lanes) (dc : destColumn < p.laneLen)
    (left : s.gpr .rdi = FillPointers.cell (matrix s) p leftLane leftColumn)
    (right : s.gpr .rsi = FillPointers.cell (matrix s) p rightLane rightColumn)
    (dest : s.gpr .r10 = FillPointers.cell (matrix s) p destLane destColumn) : FillCompress.Ready s := by
  have leftSub := cell_sub p (matrix s) positive ll lc
  have rightSub := cell_sub p (matrix s) positive rl rc
  have destSub := cell_sub p (matrix s) positive dl dc
  have read (lane column : Nat) (hl : lane < p.lanes) (hc : column < p.laneLen) :
      Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩] (s.rd ++ s.wr) := by
    intro a n ha
    obtain ⟨r, hr, hc⟩ := layout.cell_cover positive hl hc a n ha
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  constructor
  · intro d hd
    exact layout.frameRead d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp)
  · exact layout.frameWrite
  · rw [left]; exact read leftLane leftColumn ll lc
  · rw [right]; exact read rightLane rightColumn rl rc
  · rw [dest]; exact layout.cell_cover positive dl dc
  · exact layout.workWrite
  · rw [left]; exact layout.matrixWork.sub_left leftSub
  · rw [right]; exact layout.matrixWork.sub_left rightSub
  · rw [dest]; exact layout.matrixWork.sub_left destSub
  · exact layout.frameWork
  · rw [left]; exact layout.matrixFrame.sub_left leftSub
  · rw [right]; exact layout.matrixFrame.sub_left rightSub
  · rw [dest]; exact layout.matrixFrame.sub_left destSub
  · rw [left]; exact (layout.matrixStack.sub_left leftSub).symm
  · rw [right]; exact (layout.matrixStack.sub_left rightSub).symm
  · exact layout.stackWork
  · rw [dest]; exact layout.matrixStack.sub_left destSub
  · exact layout.frameStack

end VG.Proof.Argon2.X86_64.FillKernel

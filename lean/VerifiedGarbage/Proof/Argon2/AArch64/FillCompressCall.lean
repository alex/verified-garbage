import VerifiedGarbage.Proof.Argon2.AArch64.Compress
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! Invoke the verified compression primitive with narrowed permissions,
retaining the surrounding matrix and derivation frame. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64

/-- Persistent registers available to the enclosing derivation loop. -/
def loopRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

structure CallReady (s : State) : Prop where
  left : Covers [⟨s.gpr .x0, 1024⟩] (s.rd ++ s.wr)
  right : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .x2, 1024⟩] s.wr
  scratch : Covers [⟨s.gpr .x3, 4096⟩] s.wr
  leftScratch : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩
  rightScratch : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩
  outputScratch : (⟨s.gpr .x2, 1024⟩ : Region).Disjoint ⟨s.gpr .x3, 4096⟩
  stackLeft : (below s.sp 8).Disjoint ⟨s.gpr .x0, 1024⟩
  stackRight : (below s.sp 8).Disjoint ⟨s.gpr .x1, 1024⟩
  stackOutput : (below s.sp 8).Disjoint ⟨s.gpr .x2, 1024⟩
  stackScratch : (below s.sp 8).Disjoint ⟨s.gpr .x3, 4096⟩

structure Called (s t : State) : Prop where
  result : Spec.Argon2.blockAt t.mem (s.gpr .x2) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.mem (s.gpr .x0)) (Spec.Argon2.blockAt s.mem (s.gpr .x1))
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩, below s.sp 8] s.mem t.mem

theorem call_hyps (s : State) (h : CallReady s) :
    compressLocal.pre (s.callEntry.withRegions [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x1, 1024⟩]
      [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩]) ∧
    Covers [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x1, 1024⟩,
      ⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x3, 4096⟩] s.wr := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun _ hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressLocal, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.x0 ∉ linkRegs),
      g _ (by decide : Reg.x1 ∉ linkRegs), g _ (by decide : Reg.x2 ∉ linkRegs),
      g _ (by decide : Reg.x3 ∉ linkRegs)]
    exact ⟨trivial, trivial, h.outputScratch, h.leftScratch, h.rightScratch⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.left p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.right p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩

theorem call_ok (name : String) (s : State) (h : CallReady s) :
    WP isa (.call name Impl.Argon2.AArch64.compress) s (Called s) := by
  obtain ⟨pre, cover, writes⟩ := call_hyps s h
  refine WP.call (k := compressLocal) compress_correct pre cover writes ?_ (by lit_decide)
  intro t rd wr sp frame regs _ result
  change Spec.Argon2.blockAt t.mem (s.callEntry.gpr .x2) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.mem (s.callEntry.gpr .x0))
    (Spec.Argon2.blockAt s.mem (s.callEntry.gpr .x1)) at result
  rw [State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs)] at result
  refine ⟨result, ?_, rd, wr, sp, frame.mono ?_⟩
  · intro r hr
    have hp : r ∈ preserved ∧ r ≠ .x30 := by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact regs r hp.1 hp.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))

end VG.Proof.Argon2.AArch64.FillCompress

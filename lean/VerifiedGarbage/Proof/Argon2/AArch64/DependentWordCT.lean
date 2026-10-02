import VerifiedGarbage.Proof.Argon2.AArch64.DependentWord
import VerifiedGarbage.Proof.Argon2.AArch64.DependentWordLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! The previous cell is read at an address determined by public parameters. -/
namespace VG.Proof.Argon2.AArch64.DependentWord
open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : FillKernel.Ready p pass lane slice index s
  right : FillKernel.Ready p pass lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t

theorem pointer_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    pointer (fun s t => s.sp = t.sp) := by
  have trace := RelCT.taintRegs (c := pointer) (τ := Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
    (P := fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)
  exact trace.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem read_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8)
    (.block Impl.Argon2.AArch64.DependentWord.read) (fun s t => s.sp = t.sp) := by
  have trace := RelCT.taintRegs (c := .block Impl.Argon2.AArch64.DependentWord.read)
    (τ := Taint.ofRegs [.x8]) (P := fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8)
    (fun _ _ h => ⟨h.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r; exact h.2⟩) [] (by taint_decide)
  exact trace.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun s t => s.sp = t.sp) := by
  have trace := pointer_rel.mono (P' := Related p pass lane slice index) (by
    intro s t h
    refine ⟨h.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.bases
    · exact h.left.position.laneLength.trans h.right.position.laneLength.symm
    · exact h.left.position.segmentLength.trans h.right.position.segmentLength.symm
    · exact h.left.position.slice.trans h.right.position.slice.symm
    · exact h.left.position.index.trans h.right.position.index.symm) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨pointer_ok s p pass lane slice index h.left, pointer_ok t p pass lane slice index h.right⟩)
  have publicTrace : RelCT isa (Related p pass lane slice index) pointer
      (fun s t => s.sp = t.sp ∧ s.gpr .x8 = t.gpr .x8) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨sp, s, t, hp, ⟨pa, _⟩, ⟨pb, _⟩⟩ := h
    have equal : FillKernel.previous s p lane slice index = FillKernel.previous t p lane slice index := by
      unfold FillKernel.previous; rw [hp.matrices]
    exact ⟨sp, pa.trans (equal.trans pb.symm)⟩)
  exact publicTrace.seq read_rel

end VG.Proof.Argon2.AArch64.DependentWord

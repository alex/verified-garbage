import VerifiedGarbage.Proof.Argon2.X86_64.DependentWord
import VerifiedGarbage.Proof.Argon2.X86_64.DependentWordLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! The previous cell is read at an address determined by public parameters. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : FillKernel.Ready p pass lane slice index s
  right : FillKernel.Ready p pass lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : FillKernel.matrix s = FillKernel.matrix t

theorem pointer_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r)
    pointer (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r12, .r13, .r14, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem read_rel : RelCT isa (fun s t => s.gpr .rax = t.gpr .rax) (.block Impl.Argon2.X86_64.DependentWord.read) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rax])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun _ _ => True) := by
  have trace := pointer_rel.mono (P' := Related p pass lane slice index) (by
    intro s t h r hr
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
      (fun s t => s.gpr .rax = t.gpr .rax) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ⟨pa, _⟩, ⟨pb, _⟩⟩ := h
    have equal : FillKernel.previous s p lane slice index = FillKernel.previous t p lane slice index := by
      unfold FillKernel.previous; rw [hp.matrices]
    exact pa.trans (equal.trans pb.symm))
  exact publicTrace.seq read_rel

end VG.Proof.Argon2.X86_64.DependentWord

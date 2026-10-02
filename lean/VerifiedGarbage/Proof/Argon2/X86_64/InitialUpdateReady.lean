import VerifiedGarbage.Proof.Argon2.X86_64.InitialCTState

/-! Permissions for the two updates of each length-prefixed H₀ input. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

theorem prefix_update_ready {s t : State} {lo : Nat} (h : Space s) (args : LengthArgs s lo t) :
    HPrime.UpdateReady t := by
  have k := args.keeps
  have ht := h.keeps k
  have len : (t.gpr .rcx).toNat = 4 := by rw [args.size]; rfl
  refine ⟨ht.work, ?_, ?_, ?_, ht.stackWork, ?_⟩
  · rw [args.pointer, len, ← k.rbx]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨t.gpr .rbx, 16384⟩, List.mem_append_right _ ht.work, 792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  · rw [args.pointer, len, k.rbx]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  · rw [args.pointer, len, k.rbx]
    exact Offset.disjoint _ (d := 792) (n := 4) (e := 192) (k := 576) (by decide) (by decide) (by decide)
  · rw [args.pointer, len, ← k.rbx]
    exact ht.stackWork.sub_right (Offset.sub_base _ (by decide))

theorem input_update_ready {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (length : s.gpr .r14 = wordAt s lo) (args : InputArgs s t po) : HPrime.UpdateReady t := by
  have k := args.keeps
  have ptr : t.gpr .rdx = wordAt s po := args.pointer
  have len : t.gpr .rcx = wordAt s lo := args.length.trans length
  refine ⟨(h.space.keeps k).work, ?_, ?_, ?_, (h.space.keeps k).stackWork, ?_⟩
  · rw [ptr, len, k.rd, k.wr]; exact h.cover
  · rw [ptr, len, k.rbx]; exact h.work.sub_right (Region.sub_prefix (by decide))
  · rw [ptr, len, k.rbx]; exact h.work.sub_right (Offset.sub_base _ (by decide))
  · rw [ptr, len, k.rsp]; exact h.stack.symm

structure LengthRelated (lo : Nat) (s t : State) : Prop where
  related : RelatedRegs [.r12, .r14] s t
  leftLength : s.gpr .r14 = wordAt s lo
  rightLength : t.gpr .r14 = wordAt t lo

theorem LengthRelated.hash_keeps {lo : Nat} {s t a b : State} (h : LengthRelated lo s t)
    (bound : lo + 8 ≤ 272) (ka : HPrime.Keeps s a) (kb : HPrime.Keeps t b) : LengthRelated lo a b := by
  refine ⟨⟨h.related.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_, ?_⟩
  · intro r hr
    have saved : ∀ r ∈ ([.r12, .r14] : List Reg), r ∈ calleeSaved := by decide
    rw [ka.regs r (saved r hr), kb.regs r (saved r hr)]
    exact h.related.2 r hr
  · rw [ka.regs .r14 (by decide), h.related.1.left.space.word_keeps (Keeps.of_hash ka) lo bound]
    exact h.leftLength
  · rw [kb.regs .r14 (by decide), h.related.1.right.space.word_keeps (Keeps.of_hash kb) lo bound]
    exact h.rightLength

end VG.Proof.Argon2.X86_64.Initial

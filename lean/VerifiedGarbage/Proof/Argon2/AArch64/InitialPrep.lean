import VerifiedGarbage.Proof.Argon2.AArch64.InitialHeader

/-! # H₀: preserving the stack across input argument preparation -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

theorem LengthArgs.keeps {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    Keeps s t := by
  refine ⟨fun r hr _ h22 => h.other r ?_, h.sp, h.rd, h.wr, ?_⟩
  · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true, ne_eq, not_true_eq_false]
  · rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide) (by decide))

theorem InputArgs.keeps {s t : State} {offset : Nat} (h : InputArgs s t offset) :
    Keeps s t := by
  refine ⟨fun r hr h20 _ => h.other r ?_, h.sp, h.rd, h.wr, ?_⟩
  · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true, ne_eq, not_true_eq_false]
  · rw [h.mem]; exact Frame.refl _ _

theorem LengthArgs.prefix {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    bytesAt t.mem (s.gpr .x24 + 792) 4 = Spec.Argon2.le32 (wordAt s offset).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl), h.mem,
    Mem.readW_writeW_self32]
  rfl

theorem LengthArgs.repr {s t : State} {offset : Nat} (h : LengthArgs s offset t)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .x24) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .x24) d := by
  rw [h.keeps.x24]
  apply Proof.Blake2.AArch64.Stream.repr_congr Proof.Blake2.AArch64.Stream.okB
    (mem := s.mem) (h := repr)
  intro i hi
  have f : Frame [⟨s.gpr .x24 + 792, 4⟩] s.mem t.mem := by
    rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  apply f.bytes (R := ⟨s.gpr .x24, 192⟩) _ (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact Offset.base_disjoint _ (by decide) (by decide)

theorem InputArgs.repr {s t : State} {offset : Nat} (h : InputArgs s t offset)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .x24) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .x24) d := by
  rw [h.keeps.x24, h.mem]; exact repr

theorem addCount_ok (s : State) :
    WP isa (.block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) s fun t =>
      t.gpr .x20 = s.gpr .x20 + s.gpr .x22 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.add, Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, show 0 < 4096 from by decide, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, fun r hr h20 _ => ?_, rfl, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .x15 := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_write, h20, hn, ite_false]

end VG.Proof.Argon2.AArch64.Initial

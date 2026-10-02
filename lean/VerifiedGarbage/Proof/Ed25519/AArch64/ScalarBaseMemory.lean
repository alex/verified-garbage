import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec

/-! Output pointer and saved registers remain outside the point workspace. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem scalarBaseSetup_ok (s : State) (hw : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarBaseSetup) s fun t => t.gpr .x0 = s.gpr .x2 ∧
      (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 ∧ Outside (s.gpr .x2) 48 8 s.mem t.mem := by
  have hw' : InRegions s.wr (off (s.gpr .x2) 48) 8 :=
    ⟨_, hw, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseSetup, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.store, addr, Size.bytes, mov, hw', Nat.reduceMod, Nat.reduceLT, Nat.reduceMul,
    and_self, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.mem_write, BitVec.setWidth_eq, write64_eq_writeW, Mem.readW_writeW_self64]
  · rw [RegUpd.mem_write, BitVec.setWidth_eq, write64_eq_writeW]
    exact writeW_outside _ _ _ (by decide)

theorem scalarBaseFinishArgs_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block scalarBaseFinishArgs) s fun t =>
      t.gpr .x2 = base ∧ t.gpr .x0 = s.mem.readW (off base 48) 64 ∧ Keeps [.x2, .x0] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    mov, ld, addr, Size.bytes, State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs.x0, hr, BitVec.setWidth_eq, BitVec.add_zero, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bytesAt32_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 32 = Spec.Ed25519.bytesAt m p 32 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 32⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.AArch64

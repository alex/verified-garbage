import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddCodec

/-! Keep the output pointer and saved registers outside the point workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Outside Keeps ea_at ea_sc)

theorem scalarBaseSetup_ok (s : State) (hw : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarBaseSetup) s fun t => t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem.readW (off (s.gpr .rdx) 48) 64 = s.gpr .rdi ∧ Outside (s.gpr .rdx) 48 8 s.mem t.mem := by
  have hw' : InRegions s.wr (off (s.gpr .rdx) 48) 8 :=
    ⟨_, hw, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseSetup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, hw', ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, ?_, ?_⟩
  · exact RegUpd.gpr_setReg_self _ _ _
  · exact RegUpd.gpr_setReg_of_ne _ _ hr
  · exact Mem.readW_writeW_self64 _ _ _
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)

theorem scalarBaseFinishArgs_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block scalarBaseFinishArgs) s fun t =>
      t.gpr .rdx = base ∧ t.gpr .rdi = s.mem.readW (off base 48) 64 ∧ Keeps [.rdx, .rdi] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hs.rdi, hr, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem bytesAt32_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 32 = Spec.Ed25519.bytesAt m p 32 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 32⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86_64

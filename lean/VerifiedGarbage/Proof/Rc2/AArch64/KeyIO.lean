import VerifiedGarbage.Proof.Rc2.AArch64.KeyBody

/-! # Register setup and scratch saves for key expansion -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

def savedReg (i : Nat) : Reg := saved.getD i .x23

theorem keySave_eq : save .x4 0 = saveCode .x4 savedReg 6 := by rfl

theorem keyRestore_eq : restore .x4 0 = restoreCode .x4 savedReg (List.range 6) := by rfl

theorem pinKey_ok (s : State) :
    ∃ s', runBlock isa [rr .x19 .x0, rr .x20 .x1, rr .x21 .x3, rr .x22 .x2, imm .x23 0] s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧
      s'.gpr .x21 = s.gpr .x3 ∧ s'.gpr .x22 = s.gpr .x2 ∧ s'.gpr .x23 = 0 ∧ Keep saved s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · exact gpr_write_self _ _ _ _
  · constructor
    · intro r hr
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, State.read, BitVec.add_zero, hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.AArch64

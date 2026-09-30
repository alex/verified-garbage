import VerifiedGarbage.Proof.Rc2.X86_64.KeyBody

/-! # Register setup and scratch saves for key expansion -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def savedReg (i : Nat) : Reg := saved.getD i .rbx

theorem keySave_eq : save .r8 0 = saveCode .r8 savedReg 6 := by rfl

theorem keyRestore_eq : restore .r8 0 = restoreCode .r8 savedReg (List.range 6) := by rfl

theorem pinKey_ok (s : State) :
    ∃ s', runBlock isa [rr .r12 .rdi, rr .r13 .rsi, rr .r14 .rcx, rr .r15 .rdx, imm .rbx 0] s = some s' ∧
      s'.gpr .r12 = s.gpr .rdi ∧ s'.gpr .r13 = s.gpr .rsi ∧
      s'.gpr .r14 = s.gpr .rcx ∧ s'.gpr .r15 = s.gpr .rdx ∧ s'.gpr .rbx = 0 ∧ Keep saved s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.X86_64

import VerifiedGarbage.Impl.Argon2.X86_64.FillIterations
import VerifiedGarbage.Proof.Argon2.X86_64.FillIteration

/-! Increment, save and compare the public pass counter. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .rax = s.mem.readW (off (s.gpr .rbp) 0) 64 + 1 ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [increment, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (off (s.gpr .rbp) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 72) 8) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      t.cf = decide ((s.gpr .rax).toNat < (s.mem.readW (off (s.gpr .rbp) 72) 64).toNat) := by
  apply WP.of_runBlock
  have sep : Mem.Sep (off (s.gpr .rbp) 72) 8 (off (s.gpr .rbp) 0) 8 :=
    Offset.sep _ (by decide) (by decide) (by decide)
  simp only [saveCheck, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.load64, ea_at, hw, hr, readSrc, execAlu, ite_true,
    Mem.readW_writeW_sep (w := 64) (w' := 64) sep (by decide), RegUpd.cf_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, trivial⟩
  rfl

end VG.Proof.Argon2.X86_64.FillIterations

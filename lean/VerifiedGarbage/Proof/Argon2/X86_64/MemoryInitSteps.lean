import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy

/-! # Public pointer advances and lane countdowns -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Advanced (s t : State) : Prop where
  destination : t.gpr .r14 = s.gpr .r14 + 1024
  other : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .r14 (.imm 1024)]) s (Advanced s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left',
    show (BitVec.signExtend 64 (1024 : BitVec 32)) = 1024 from rfl]
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hr, ite_false]

structure LaneEnd (s t : State) : Prop where
  destination : t.gpr .r14 = s.gpr .r14 + s.gpr .r13 - 1024
  lane : t.gpr .r12 = s.gpr .r12 + 1
  remaining : t.gpr .r15 = s.gpr .r15 - 1
  zf : t.zf = some (s.gpr .r15 - 1 == 0)
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem laneEnd_ok (s : State) :
    WP isa (.block [.alu .add .r14 (.reg .r13), .alu .sub .r14 (.imm 1024),
      .alu .add .r12 (.imm 1), .alu .sub .r15 (.imm 1)]) s (LaneEnd s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left',
    show (BitVec.signExtend 64 (1024 : BitVec 32)) = 1024 from rfl,
    show (BitVec.signExtend 64 (1 : BitVec 32)) = 1 from rfl]
  refine ⟨rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, h1, h2, h3, ite_false]

end VG.Proof.Argon2.X86_64.MemoryInit

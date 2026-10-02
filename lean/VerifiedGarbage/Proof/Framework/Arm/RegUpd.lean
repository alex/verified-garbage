import VerifiedGarbage.TCB.Arm.Isa

/-!
# ARMv7: reading a state after a write, for symbolic execution

The registers of a state after a write, read one write at a time, with
`State.setReg` kept folded, as in `VG.X86_64.RegUpd` (which explains why):
`gpr_setReg` for registers that are literals, `gpr_setReg_self` and
`gpr_setReg_of_ne` for variables.
-/

namespace VG.Arm.RegUpd

variable (s : State)

theorem gpr_setReg (d : Reg) (x : BitVec 32) (r : Reg) :
    (s.setReg d x).gpr r = if r = d then x else s.gpr r := rfl

theorem gpr_setReg_self (r : Reg) (x : BitVec 32) : (s.setReg r x).gpr r = x := by
  simp [State.setReg]

theorem gpr_setReg_of_ne {r r' : Reg} (x : BitVec 32) (h : ¬r' = r) :
    (s.setReg r x).gpr r' = s.gpr r' := by
  simp [State.setReg, h]

theorem mem_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).mem = s.mem := rfl
theorem rd_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).rd = s.rd := rfl
theorem wr_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).wr = s.wr := rfl
theorem sp_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).sp = s.sp := rfl
theorem z_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).z = s.z := rfl
theorem n_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).n = s.n := rfl
theorem c_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).c = s.c := rfl
theorem v_setReg (r : Reg) (x : BitVec 32) : (s.setReg r x).v = s.v := rfl

end VG.Arm.RegUpd

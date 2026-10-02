import VerifiedGarbage.TCB.X86.Isa

/-!
# x86 (32-bit): reading a state after a write, for symbolic execution

The registers and flags of a state after a write, read one write at a time,
with `State.setReg`, `State.setFlags` and `arithFlags` kept folded, as in
`VG.X86_64.RegUpd` (which explains why): `gpr_setReg` for registers that are
literals, `gpr_setReg_self` and `gpr_setReg_of_ne` for variables.
-/

namespace VG.X86.RegUpd

variable (s : State)

/-! ## `setReg` -/

theorem gpr_setReg (d : Reg) (v : BitVec 32) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then v else s.gpr r := rfl

theorem gpr_setReg_self (r : Reg) (v : BitVec 32) : (s.setReg r v).gpr r = v := by
  simp [State.setReg]

theorem gpr_setReg_of_ne {r r' : Reg} (v : BitVec 32) (h : ¬r' = r) :
    (s.setReg r v).gpr r' = s.gpr r' := by
  simp [State.setReg, h]

theorem mem_setReg (r : Reg) (v : BitVec 32) : (s.setReg r v).mem = s.mem := rfl
theorem rd_setReg (r : Reg) (v : BitVec 32) : (s.setReg r v).rd = s.rd := rfl
theorem wr_setReg (r : Reg) (v : BitVec 32) : (s.setReg r v).wr = s.wr := rfl
theorem zf_setReg (r : Reg) (v : BitVec 32) : (s.setReg r v).zf = s.zf := rfl
theorem cf_setReg (r : Reg) (v : BitVec 32) : (s.setReg r v).cf = s.cf := rfl

/-! ## `setFlags` and `arithFlags` -/

theorem gpr_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).gpr = s.gpr := rfl
theorem mem_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).mem = s.mem := rfl
theorem rd_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).rd = s.rd := rfl
theorem wr_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).wr = s.wr := rfl

theorem gpr_arithFlags (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).gpr = s.gpr := rfl
theorem mem_arithFlags (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).mem = s.mem := rfl
theorem rd_arithFlags (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).rd = s.rd := rfl
theorem wr_arithFlags (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).wr = s.wr := rfl
theorem zf_arithFlags (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).zf = some (x == 0) := rfl
theorem cf_arithFlags (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).cf = some c := rfl

end VG.X86.RegUpd

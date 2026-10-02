import VerifiedGarbage.TCB.AArch64.Isa

/-!
# AArch64: reading a state after a write, for symbolic execution

The registers of a state after a write, read one write at a time, with
`State.write` kept folded, as in `VG.X86_64.RegUpd` (which explains why):
`gpr_write` for registers that are literals, `gpr_write_self` and
`gpr_write_of_ne` for variables.
-/

namespace VG.AArch64.RegUpd

variable (s : State)

theorem gpr_write (sz : Size) (d : Reg) (v : BitVec sz.bits) (r : Reg) :
    (s.write sz d v).gpr r = if r = d then v.setWidth 64 else s.gpr r := rfl

theorem gpr_write_self (sz : Size) (r : Reg) (v : BitVec sz.bits) :
    (s.write sz r v).gpr r = v.setWidth 64 := by
  simp [State.write]

theorem gpr_write_of_ne (sz : Size) {r r' : Reg} (v : BitVec sz.bits) (h : ¬r' = r) :
    (s.write sz r v).gpr r' = s.gpr r' := by
  simp [State.write, h]

theorem mem_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).mem = s.mem := rfl
theorem rd_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).rd = s.rd := rfl
theorem wr_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).wr = s.wr := rfl
theorem sp_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).sp = s.sp := rfl
theorem c_write (sz : Size) (r : Reg) (v : BitVec sz.bits) : (s.write sz r v).c = s.c := rfl

theorem gpr_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) (r : Reg) :
    (s.addWithCarry sz d a b c).gpr r =
      if r = d then (a + b + BitVec.ofNat sz.bits c.toNat).setWidth 64 else s.gpr r := rfl

theorem c_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).c = decide (2 ^ sz.bits ≤ a.toNat + b.toNat + c.toNat) := rfl

theorem mem_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).mem = s.mem := rfl
theorem rd_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).rd = s.rd := rfl
theorem wr_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).wr = s.wr := rfl
theorem sp_addWithCarry (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).sp = s.sp := rfl

theorem v_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (s.write sz r x).v = s.v := rfl

theorem v_setV (d : VReg) (x : BitVec 128) (r : VReg) :
    (s.setV d x).v r = if r = d then x else s.v r := rfl

theorem v_setV_self (r : VReg) (x : BitVec 128) : (s.setV r x).v r = x := by
  simp [State.setV]

theorem v_setV_of_ne {r r' : VReg} (x : BitVec 128) (h : r' ≠ r) :
    (s.setV r x).v r' = s.v r' := by simp [State.setV, h]

theorem gpr_setV (r : VReg) (x : BitVec 128) : (s.setV r x).gpr = s.gpr := rfl
theorem mem_setV (r : VReg) (x : BitVec 128) : (s.setV r x).mem = s.mem := rfl
theorem rd_setV (r : VReg) (x : BitVec 128) : (s.setV r x).rd = s.rd := rfl
theorem wr_setV (r : VReg) (x : BitVec 128) : (s.setV r x).wr = s.wr := rfl
theorem sp_setV (r : VReg) (x : BitVec 128) : (s.setV r x).sp = s.sp := rfl

end VG.AArch64.RegUpd

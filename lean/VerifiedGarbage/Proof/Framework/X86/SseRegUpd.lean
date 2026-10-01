import VerifiedGarbage.Proof.Framework.X86.RegUpd

namespace VG.X86.RegUpd
variable (s : State)

/-! ## SIMD register writes, kept folded during symbolic execution -/

theorem xmm_setReg (r : Reg) (v : BitVec 32) : (s.setReg r v).xmm = s.xmm := rfl

theorem xmm_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).xmm = s.xmm := rfl

theorem xmm_arithFlags (x : BitVec 32) (c o : Bool) : (arithFlags s x c o).xmm = s.xmm := rfl

theorem xmm_setXmm (d : XReg) (v : BitVec 128) (r : XReg) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl

theorem xmm_setXmm_self (r : XReg) (v : BitVec 128) : (s.setXmm r v).xmm r = v := by
  rw [xmm_setXmm, ite_eq_left (by rfl)]

theorem xmm_setXmm_of_ne {r r' : XReg} (v : BitVec 128) (h : ¬r' = r) :
    (s.setXmm r v).xmm r' = s.xmm r' := by
  rw [xmm_setXmm, ite_eq_right h]

theorem gpr_setXmm (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
theorem mem_setXmm (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
theorem rd_setXmm (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
theorem wr_setXmm (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl
theorem zf_setXmm (r : XReg) (v : BitVec 128) : (s.setXmm r v).zf = s.zf := rfl
theorem cf_setXmm (r : XReg) (v : BitVec 128) : (s.setXmm r v).cf = s.cf := rfl

end VG.X86.RegUpd

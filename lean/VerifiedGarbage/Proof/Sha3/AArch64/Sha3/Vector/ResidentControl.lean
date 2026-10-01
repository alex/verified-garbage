import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSelect
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

theorem advance_test_ok (s : State) (p : Addr) (n r : Nat)
    (_hn : n < 2^64) (hr : r ≤ n) (hrb : r ≤ 168) (hu : n < 2^63+r)
    (h3 : s.gpr .x3 = p) (h4 : s.gpr .x4 = BitVec.ofNat 64 n)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 r) :
    WP isa (.block (advance ++ test)) s fun s' =>
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.v = s.v ∧
      s'.gpr .x3 = p + BitVec.ofNat 64 r ∧
      s'.gpr .x4 = BitVec.ofNat 64 (n-r) ∧ s'.gpr .x6 = s.gpr .x6 ∧
      isa.eval (.zero .x .x7) s' = some (decide (r ≤ n-r)) := by
  unfold advance test
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons (exec_lsr_x (by decide)) (wp_nil ?_))))
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 r = BitVec.ofNat 64 (n-r) :=
    VG.Proof.Sha3.sub_ofNat hr
  simp (config := {decide := true}) only [
    RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write,RegUpd.v_write,
    RegUpd.gpr_write,ite_true,ite_false,State.read,Size.bits,BitVec.setWidth_eq,h3,h4,h6,hsub,
    true_and]
  simp only [eval_zero,RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq,decide_eq_true_eq,enough_iff (n-r) r (by omega) hrb]
  exact and_iff_left (by omega)

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit

/-! Straight-line and fixed-loop pieces of public point decoding. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem r0_agree {b : BitVec 32} {x y : State} (hx : x.gpr .r0 = b) (hy : y.gpr .r0 = b) :
    ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r := by
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hx.trans hy.symm

theorem returnFlag_ct (b : Bool) :
    CT (fun _ _ => True) (.block [.mov .r9 (.imm b.toNat)]) (fun _ _ => True) := by
  cases b <;> apply ctRegs [] _ (by taint_decide)
  all_goals intro _ _ _ r h; exact (List.not_mem_nil h).elim

theorem recoverInvalid_ct : CT (fun _ _ => True) recoverInvalid (fun _ _ => True) := returnFlag_ct false

theorem recoverSuccess_ct (base : BitVec 32) :
    CT (fun x y => x.gpr .r0 = base ∧ y.gpr .r0 = base) recoverSuccess (fun _ _ => True) := by
  apply ctRegs [.r0] _ (by taint_decide)
  exact fun _ _ h => r0_agree h.1 h.2

end VG.Proof.Ed25519.Arm

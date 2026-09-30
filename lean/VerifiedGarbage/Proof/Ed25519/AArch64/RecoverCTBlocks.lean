import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint

/-! Untrusted: fixed-trace arithmetic blocks used in point recovery. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem x0_agree {base : Addr} {s t : State} (hs : s.gpr .x0 = base) (ht : t.gpr .x0 = base) :
    ∀ r ∈ Taint.ofRegs [.x0], s.gpr r = t.gpr r := agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) recoverCandidate (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem parityBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (freeze (offset 0) ++ recoverParity)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem zeroBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem negateBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem successBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem recoverInvalid_ct : CT (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
  exact fun _ _ _ => agree_ofRegs (by simp)

end VG.Proof.Ed25519.AArch64

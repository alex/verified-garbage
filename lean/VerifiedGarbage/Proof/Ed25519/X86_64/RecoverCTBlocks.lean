import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverPoint

/-! Untrusted: fixed-trace arithmetic blocks used in point recovery. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem rdi_agree {base : Addr} {s t : State} (hs : s.gpr .rdi = base) (ht : t.gpr .rdi = base) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t := Taint.agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) recoverCandidate (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem parityBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem zeroBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem negateBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem successBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem recoverInvalid_ct : RelCT isa (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  exact fun _ _ _ => Taint.agree_ofRegs (by simp)

end VG.Proof.Ed25519.X86_64

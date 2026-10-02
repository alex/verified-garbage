import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Ed25519.X86.RecoverPoint

/-! Fixed-trace arithmetic blocks used in point recovery. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem edi_agree {base : BitVec 32} {s t : State} (hs : s.gpr .edi = base) (ht : t.gpr .edi = base) :
    VG.X86.Taint.Agree (regsTaint [.edi]) s t := regsTaint_agree (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base) recoverCandidate (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem parityBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem zeroBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem negateBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem successBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem recoverInvalid_ct : RelCT isa (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
  exact fun _ _ _ => regsTaint_agree (by simp)

end VG.Proof.Ed25519.X86

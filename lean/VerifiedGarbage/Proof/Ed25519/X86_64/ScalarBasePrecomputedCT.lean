import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedEngine
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem scalarBasePrecomputedEngine_ct (base k : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      (scalarBasePrecomputedEngine fld) (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      (scalarBasePrepare fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hp := withRuns hc (fun x y h =>
    ⟨scalarBasePrepare_ok h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     scalarBasePrepare_ok h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [scalarBasePrecomputedEngine]
  refine VG.RelCT.seq hp ?_
  intro x y tx ty x' y' ⟨_, a, b, hab, hx, hy⟩ ex ey
  have hct : RelCT isa (fun u v =>
      (Scratch u base ∧ env u.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, u.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) < 2 ^ (16 * 16)) ∧
      (Scratch v base ∧ env v.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, v.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) < 2 ^ (16 * 16)))
      (combMultiply fld) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi) (by fld_taint_decide)
  have hm' := withRuns hct (fun u v h =>
    ⟨combMultiply_ok (fld := fld) h.1.1 h.1.2.2.2 h.1.2.1 h.1.2.2.1,
     combMultiply_ok (fld := fld) h.2.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1⟩)
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base)
      (pointEncode fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro u v h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.trans h.2.symm)
  have hm'' := hm'.mono (fun _ _ h => h) (fun u v ⟨_, c, d, hcd, hu, hv⟩ =>
      And.intro (hu.2.scratch hcd.1.1).rdi (hv.2.scratch hcd.2.1).rdi)
  exact (VG.RelCT.seq hm'' he) _ _ _ _ _ _
    ⟨⟨hx.1.scratch hab.1.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩,
     ⟨hy.1.scratch hab.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2⟩⟩ ex ey

theorem scalarBase_precomputed_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub
    (scalarBase_precomputed fld) :=
  scalarBase_ct_of_engine (scalarBasePrecomputedEngine fld) scalarBasePrecomputedEngine_ok
    scalarBasePrecomputedEngine_ct

end VG.Proof.Ed25519.X86_64

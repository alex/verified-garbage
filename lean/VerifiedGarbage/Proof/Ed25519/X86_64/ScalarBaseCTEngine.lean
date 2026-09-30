import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine

/-! Untrusted: expand secret scalar bits, multiply, and encode with a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

def BaseEnginePre (base k : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    ∀ q < 32, 8192 ≤ ofs base (off k q)

theorem scalarBaseEngine_ct (base k : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      scalarBaseEngine (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      scalarBasePrepare (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi]) _ (by taint_decide)
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
  rw [scalarBaseEngine]
  refine VG.RelCT.seq hp ?_
  intro x y tx ty x' y' ⟨_, a, b, hab, hx, hy⟩ ex ey
  have hm := pointMultiply16_ct base
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32))
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32))
  have hm' := withRuns hm (fun u v h =>
    ⟨pointMultiply_ok h.1.1 16 _ (by decide) (by decide) h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     pointMultiply_ok h.2.1 16 _ (by decide) (by decide) h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base)
      pointEncode (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    intro u v h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.trans h.2.symm)
  have hm'' := hm'.mono (fun _ _ h => h) (fun u v ⟨_, c, d, hcd, hu, hv⟩ =>
      And.intro (hu.2.2.scratch hcd.1.1).rdi (hv.2.2.scratch hcd.2.1).rdi)
  exact (VG.RelCT.seq hm'' he) _ _ _ _ _ _
    ⟨⟨hx.1.scratch hab.1.1, hx.2.2.2.2, hx.2.2.1, hx.2.2.2.1⟩,
     ⟨hy.1.scratch hab.2.1, hy.2.2.2.2, hy.2.2.1, hy.2.2.2.1⟩⟩ ex ey

end VG.Proof.Ed25519.X86_64

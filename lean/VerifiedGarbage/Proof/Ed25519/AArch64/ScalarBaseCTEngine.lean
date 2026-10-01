import VerifiedGarbage.Proof.Ed25519.AArch64.BaseMultiplyCT
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine

/-! Untrusted: expand secret scalar bits, multiply, and encode with a public trace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def BaseEnginePre (base k : Addr) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    ∀ q < 32, 8192 ≤ ofs base (off k q)

theorem scalarBaseEngine_ct (base k : Addr) :
    CT (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      scalarBaseEngine (fun _ _ => True) := by
  have hc : CT (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      scalarBasePrepare (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.x0.trans h.2.1.x0.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hp := withRuns hc (fun x y h =>
    ⟨scalarBasePrepare_ok h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     scalarBasePrepare_ok h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [scalarBaseEngine]
  refine CT.seq hp ?_
  intro x y tx ty x' y' ⟨hsp, _, a, b, hab, hx, hy⟩ ex ey
  have hm := baseMultiply_ct base
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32))
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32))
  have hm' := withRuns hm (fun u v h =>
    ⟨baseMultiply_ok h.1.1 _ h.1.2.1 h.1.2.2, baseMultiply_ok h.2.1 _ h.2.2.1 h.2.2.2⟩)
  have he : CT (fun u v => u.gpr .x0 = base ∧ v.gpr .x0 = base)
      pointEncode (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro u v h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.trans h.2.symm)
  have hm'' := hm'.mono (fun _ _ h => h) (fun u v ⟨_, c, d, hcd, hu, hv⟩ =>
      And.intro (hu.2.scratch hcd.1.1).x0 (hv.2.scratch hcd.2.1).x0)
  exact (CT.seq hm'' he) _ _ _ _ _ _
    ⟨hsp, ⟨hx.1.scratch hab.1.1, hx.2.2, hx.2.1⟩, ⟨hy.1.scratch hab.2.1, hy.2.2, hy.2.1⟩⟩ ex ey

end VG.Proof.Ed25519.AArch64

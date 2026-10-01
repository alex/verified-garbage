import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem pointEncode_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi)
    pointEncode (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

theorem accumulate16_ct (x : BitVec 32) : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 28 = wd t.mem x 28)
    accumulate16 (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (pointTaint 28) _ (by taint_decide)
  intro s t h
  exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

def PowersCTPre (x : BitVec 32) (s t : State) : Prop :=
  PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 24 = wd t.mem x 24

theorem powersBody16_ct (x : BitVec 32) : RelCT isa (PowersCTPre x)
    (powersBody 1024 16 true) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (pointTaint 24) _ (by taint_decide)
  intro s t h
  exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem powersBody32_ct (x : BitVec 32) : RelCT isa (PowersCTPre x)
    (powersBody 1024 32 true) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (pointTaint 24) _ (by taint_decide)
  intro s t h
  exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem powersBodyLocal_ct (x : BitVec 32) : RelCT isa (PowersCTPre x)
    (powersBody 5120 16 false) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (pointTaint 24) _ (by taint_decide)
  intro s t h
  exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

theorem accumulate16_ct_regs (x : BitVec 32) : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 28 = wd t.mem x 28)
    accumulate16 (fun s t => s.gpr .edi = t.gpr .edi) := by
  have h : RelCT isa (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ wd s.mem x 28 = wd t.mem x 28) accumulate16 (fun s t => ∀ r ∈ ([.edi] : List Reg), s.gpr r = t.gpr r) := by
    apply ctTaintRegs (τ := pointTaint 28) _ [.edi] (by taint_decide)
    intro s t h
    exact pointTaint_agree h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2
  exact h.mono (fun _ _ h => h) (fun _ _ h => h .edi (List.mem_singleton_self _))

end VG.Proof.Ed25519.X86

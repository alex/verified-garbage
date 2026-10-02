import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# TDEA-CMAC on AArch64: constant time

Untrusted: everything here is checked by Lean. The taint analysis
(`Framework/AArch64/Taint.lean`) checks that only the arguments, which are
public, decide branches and addresses: the functions keep their pointers
and counts in registers.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64

theorem init_ct : ConstantTime isa initAArch64.pre initAArch64.pub Impl.CmacTripleDes.AArch64.init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem update_ct : ConstantTime isa updateAArch64.pre updateAArch64.pub Impl.CmacTripleDes.AArch64.update := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem finalize_ct :
    ConstantTime isa finalizeAArch64.pre finalizeAArch64.pub Impl.CmacTripleDes.AArch64.finalize := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

end VG.Proof.CmacTripleDes.AArch64

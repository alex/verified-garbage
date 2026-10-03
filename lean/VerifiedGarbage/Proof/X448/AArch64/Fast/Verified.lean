import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.X448.AArch64.Fast.Main
import VerifiedGarbage.Proof.X448.AArch64.Fast.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X448 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant or a counter), satisfiability, and the shared
contract of `Spec/`.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Proof.X448.AArch64 (Pre)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448AArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Fast.x448 s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448AArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448AArch64.pre Proof.X448.x448AArch64.pub
    Impl.X448.AArch64.Fast.x448 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem x448_verified :
    Verified AArch64.target Impl.X448.AArch64.Fast.x448 (Spec.X448.x448Contract AArch64.abi) :=
  Verified.of_correct x448_ok x448_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, AArch64.abi, AArch64.argRegs,
      Proof.X448.x448AArch64] [satState] using satState)

end VG.Proof.X448.AArch64.Fast

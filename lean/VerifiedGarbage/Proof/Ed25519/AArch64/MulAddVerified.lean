import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMain
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddLit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-! Untrusted: scalar multiply-add satisfies the merged specification, ABI, and constant-time contract. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def mulAddSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x5000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  scalarMulAdd_correct (MulAddPre.of hs)

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem scalarMulAdd_verified : Verified AArch64.target scalarMulAdd
    (Spec.Ed25519.scalarMulAddContract AArch64.abi) :=
  Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (by
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, scalarMulAddLocal]
      [mulAddSatState] using mulAddSatState)

end VG.Proof.Ed25519.AArch64

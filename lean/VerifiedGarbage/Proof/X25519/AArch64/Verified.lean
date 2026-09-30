import VerifiedGarbage.Proof.X25519.AArch64.Top
import VerifiedGarbage.Proof.X25519.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X25519 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant, or the working space plus a counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.X25519.x25519AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519AArch64.pre Proof.X25519.x25519AArch64.pub
    Impl.X25519.AArch64.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem x25519_verified :
    Verified AArch64.target Impl.X25519.AArch64.x25519 (Spec.X25519.x25519Contract AArch64.abi) :=
  Verified.of_correct x25519_ok x25519_ct
    (by sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, AArch64.abi, AArch64.argRegs,
      Proof.X25519.x25519AArch64]
      [sat] using sat)

end VG.Proof.X25519.AArch64

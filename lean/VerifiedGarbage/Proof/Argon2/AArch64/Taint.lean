import VerifiedGarbage.Proof.Argon2.AArch64.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.Lit

/-! Constant-time compression: memory contents never determine an address or branch. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64

def initialTaint : AArch64.Taint.T := Taint.ofRegs [.x0, .x1, .x2, .x3]

theorem initial_agree {s t : State} (hp : compressLocal.pub s t) :
    AArch64.Taint.Agree initialTaint s t := by
  obtain ⟨h0, h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [initialTaint, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.AArch64.compress :=
  VG.Taint.constantTime (A := taint) initialTaint (fun _ _ _ _ hp => initial_agree hp)
    (by taint_decide)
end VG.Proof.Argon2.AArch64

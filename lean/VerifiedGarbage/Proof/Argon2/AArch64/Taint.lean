import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Merged from `Proof.Argon2.AArch64.Lit`. -/
section
/-! # Argon2 compression as a checked instruction literal -/

namespace VG.Proof.Argon2.AArch64

materialize_code compress := Impl.Argon2.AArch64.compress

end VG.Proof.Argon2.AArch64
end

/-! Merged from `Proof.Argon2.AArch64.Contract`. -/
section
/-! # A local contract for Argon2 block compression -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .x0, 1024⟩
    let y : Region := ⟨s.gpr .x1, 1024⟩
    let out : Region := ⟨s.gpr .x2, 1024⟩
    let scratch : Region := ⟨s.gpr .x3, 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch
  post s t := blockAt t.mem (s.gpr .x2) =
    compress (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.sp = t.sp

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩, ⟨0x4000, 4096⟩]

theorem compress_implies : compressLocal.Implies (compressContract AArch64.abi) := by
  sig_implies [compressContract, compressSig, compressLocal, AArch64.abi, AArch64.argRegs]
    [satState] using satState

end VG.Proof.Argon2.AArch64
end

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

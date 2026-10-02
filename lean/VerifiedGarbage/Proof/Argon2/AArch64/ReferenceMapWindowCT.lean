import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStartCT
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceCount

/-! The chronological window branches only on the public pass and slice. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

def PublicPosition (s t : State) : Prop :=
  s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x22, .x21], s.gpr r = t.gpr r

theorem window_rel : RelCT isa PublicPosition window (fun s t => s.sp = t.sp) := by
  have start := ReferenceStart.code_rel.wpDep (fun s t _ =>
    ⟨ReferenceStart.code_ok s, ReferenceStart.code_ok t⟩)
  refine start.seq (ReferenceCount.code_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨eq.1, (ha.2.regs .x5 (by decide)).trans
    ((hp.2 .x5 (by simp)).trans (hb.2.regs .x5 (by decide)).symm)⟩

end VG.Proof.Argon2.AArch64.ReferenceMap

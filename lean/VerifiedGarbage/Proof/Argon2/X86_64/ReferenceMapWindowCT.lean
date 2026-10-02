import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStartCT
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceCount

/-! The chronological window branches only on the public pass and slice. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

def PublicPosition (s t : State) : Prop :=
  ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r

theorem window_rel : RelCT isa PublicPosition window (fun _ _ => True) := by
  have start := ReferenceStart.code_rel.wpDep (fun s t _ =>
    ⟨ReferenceStart.code_ok s, ReferenceStart.code_ok t⟩)
  refine start.seq (ReferenceCount.code_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact (ha.2.regs .r9 (by decide)).trans
    ((hp .r9 (by simp)).trans (hb.2.regs .r9 (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReferenceMap

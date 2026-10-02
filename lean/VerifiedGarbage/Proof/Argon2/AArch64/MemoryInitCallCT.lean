import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitCall

/-! # Initialization's H′ calls leak only their public argument registers -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)

theorem hPrime_call_rel (v : HPrime.Backend) (name : String)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .x1 = 72 ∧ t.gpr .x1 = 72 ∧ s.gpr .x3 = 1024 ∧ t.gpr .x3 = 1024 ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x2 = t.gpr .x2 ∧
      s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp) :
    RelCT isa P (.call name (code v.hash)) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, r8, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := hPrime_call_hyps s hs ls os
  obtain ⟨pt, ct, wt⟩ := hPrime_call_hyps t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧
    s.callEntry.gpr .x4 = t.callEntry.gpr .x4 ∧
    s.callEntry.sp = t.callEntry.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, r8, sp⟩

end VG.Proof.Argon2.AArch64.MemoryInit

import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Compression calls reveal only their argument addresses and stack pointer. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64

theorem call_rel (name : String) {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
      s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.sp = t.sp) :
    RelCT isa P (.call name Impl.Argon2.AArch64.compress) (fun _ _ => True) := by
  apply RelCT.callEx (k := compressLocal) compress_correct compress_ct
  intro s t hp
  obtain ⟨hs, ht, di, si, dx, cx, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := call_hyps s hs
  obtain ⟨pt, ct, wt⟩ := call_hyps t ht
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧ s.sp = t.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs)]
  exact ⟨di, si, dx, cx, sp⟩

end VG.Proof.Argon2.AArch64.FillCompress

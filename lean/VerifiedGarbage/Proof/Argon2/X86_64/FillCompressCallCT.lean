import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall

/-! Compression calls reveal only their argument addresses and stack pointer. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64

theorem call_rel (name : String) {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
      s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .rsp = t.gpr .rsp) :
    RelCT isa P (.call name Impl.Argon2.X86_64.compress) (fun _ _ => True) := by
  apply RelCT.callEx (k := compressLocal) compress_correct compress_ct
  intro s t hp
  obtain ⟨hs, ht, di, si, dx, cx, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := call_hyps s hs
  obtain ⟨pt, ct, wt⟩ := call_hyps t ht
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt, sp⟩
  change s.callEntry.gpr .rdi = t.callEntry.gpr .rdi ∧
    s.callEntry.gpr .rsi = t.callEntry.gpr .rsi ∧
    s.callEntry.gpr .rdx = t.callEntry.gpr .rdx ∧
    s.callEntry.gpr .rcx = t.callEntry.gpr .rcx
  simp only [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
  exact ⟨di, si, dx, cx⟩

end VG.Proof.Argon2.X86_64.FillCompress

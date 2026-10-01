import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitCall

/-! # Initialization's H′ calls leak only their public argument registers -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (code)

theorem hPrime_call_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .rsi = 72 ∧ t.gpr .rsi = 72 ∧ s.gpr .rcx = 1024 ∧ t.gpr .rcx = 1024 ∧
      s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rdx = t.gpr .rdx ∧
      s.gpr .r8 = t.gpr .r8 ∧ s.gpr .rsp = t.gpr .rsp) :
    RelCT isa P (.call name (code (HPrime.hash v))) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, r8, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := hPrime_call_hyps s hs ls os
  obtain ⟨pt, ct, wt⟩ := hPrime_call_hyps t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt, sp⟩
  change s.callEntry.gpr .rdi = t.callEntry.gpr .rdi ∧
    s.callEntry.gpr .rsi = t.callEntry.gpr .rsi ∧
    s.callEntry.gpr .rdx = t.callEntry.gpr .rdx ∧
    s.callEntry.gpr .rcx = t.callEntry.gpr .rcx ∧
    s.callEntry.gpr .r8 = t.callEntry.gpr .r8 ∧
    s.callEntry.gpr .rsp = t.callEntry.gpr .rsp
  simp only [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, r8, congrArg (· - 8) sp⟩

end VG.Proof.Argon2.X86_64.MemoryInit

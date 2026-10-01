import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitBlock
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitCallCT

/-! # Public registers survive each initialization H′ call -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

def AgreeSaved (s t : State) : Prop := ∀ r ∈ calleeSaved, s.gpr r = t.gpr r

theorem blockArgs_rel (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa AgreeSaved (.block (blockArgs column)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) check

theorem block_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name (HPrime.hash v) column) AgreeSaved := by
  let P := fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t
  have args := ((blockArgs_rel column ct).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp => by
      exact ⟨blockArgs_ok s column (hp.1.prefix 64 (by decide)) (hp.1.prefix 68 (by decide)),
        blockArgs_ok t column (hp.2.1.prefix 64 (by decide)) (hp.2.1.prefix 68 (by decide))⟩)
  have call := hPrime_call_rel v name (P := fun a b =>
      True ∧ ∃ s t, P s t ∧ BlockArgs s a column ∧ BlockArgs t b column) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.ready hp.1, hb.ready hp.2.1, ha.inputLength, hb.inputLength,
      ha.outputLength, hb.outputLength, ?_, ?_, ?_, ?_⟩
    · exact ha.input.trans ((hp.2.2 .rbp (by decide)).trans hb.input.symm)
    · exact ha.output.trans ((hp.2.2 .r14 (by decide)).trans hb.output.symm)
    · exact ha.work.trans ((hp.2.2 .rbx (by decide)).trans hb.work.symm)
    · exact (ha.regs .rsp (by decide)).trans
        ((hp.2.2 .rsp (by decide)).trans (hb.regs .rsp (by decide)).symm))
  have full := (args.seq call).wpDep (fun s t hp =>
    ⟨block_ok v name s column hp.1, block_ok v name t column hp.2.1⟩)
  exact full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    intro r hr
    exact (ha.regs r hr).trans ((hp.2.2 r hr).trans (hb.regs r hr).symm))

theorem blocks_rel (v : Proof.Blake2.X86_64.Backend) (name : String) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name (HPrime.hash v) 0) AgreeSaved ∧
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name (HPrime.hash v) 1) AgreeSaved :=
  ⟨block_rel v name 0 ⟨_, by taint_decide⟩,
    block_rel v name 1 ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.X86_64.MemoryInit

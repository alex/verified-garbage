import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitBlock
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitCallCT

/-! # Public registers survive each initialization H′ call -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

def savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

def AgreeSaved (s t : State) : Prop := HPrime.AgreeRegs savedRegs s t

theorem blockArgs_rel (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs savedRegs)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa AgreeSaved (.block (blockArgs column)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs savedRegs)
    (fun _ _ h => h.taint) check

theorem block_rel (v : HPrime.Backend) (name : String) (column : Nat) (columnBound : column < 65536)
    (ct : ∃ hint, (taint.check (Taint.ofRegs savedRegs)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name v.hash column) AgreeSaved := by
  let P := fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t
  have args := ((blockArgs_rel column ct).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp => by
      exact ⟨blockArgs_ok s column columnBound (hp.1.prefix 64 (by decide)) (hp.1.prefix 68 (by decide)),
        blockArgs_ok t column columnBound (hp.2.1.prefix 64 (by decide)) (hp.2.1.prefix 68 (by decide))⟩)
  have call := hPrime_call_rel v name (P := fun a b =>
      True ∧ ∃ s t, P s t ∧ BlockArgs s a column ∧ BlockArgs t b column) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.ready hp.1, hb.ready hp.2.1, ha.inputLength, hb.inputLength,
      ha.outputLength, hb.outputLength, ?_, ?_, ?_, ?_⟩
    · exact ha.input.trans ((hp.2.2.2 .x19 (by decide)).trans hb.input.symm)
    · exact ha.output.trans ((hp.2.2.2 .x22 (by decide)).trans hb.output.symm)
    · exact ha.work.trans ((hp.2.2.2 .x24 (by decide)).trans hb.work.symm)
    · exact ha.sp.trans (hp.2.2.1.trans hb.sp.symm))
  have full := (args.seq call).wpDep (fun s t hp =>
    ⟨block_ok v name s column columnBound hp.1, block_ok v name t column columnBound hp.2.1⟩)
  exact full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.sp.trans (hp.2.2.1.trans hb.sp.symm), ?_⟩
    intro r hr
    have saved : ∀ r ∈ savedRegs, r ∈ FillCompress.loopRegs := by decide
    exact (ha.regs r (saved r hr)).trans ((hp.2.2.2 r hr).trans (hb.regs r (saved r hr)).symm))

theorem blocks_rel (v : HPrime.Backend) (name : String) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name v.hash 0) AgreeSaved ∧
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name v.hash 1) AgreeSaved :=
  ⟨block_rel v name 0 (by decide) ⟨_, by taint_decide⟩,
    block_rel v name 1 (by decide) ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.AArch64.MemoryInit

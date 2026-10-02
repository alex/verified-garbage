import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Init
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbCT
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Finish
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# Streaming AES-CMAC on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with 16 bytes of stack: the return addresses of the
call of a CMAC function and of its call of `vg_aes_ctr32`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (update_mx subkeys_mx finalize_mx update_spSafe subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs, v.expandMxcsr, subkeys_mx v]; decide +kernel

theorem absorb_mx (v : Ctr32Impl) : (absorb v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.allInstrs, update_mx v]
  decide +kernel

theorem finish_mx (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_mx v]; decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem absorb_spSafe (v : Ctr32Impl) :
    (absorb v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.all, update_spSafe v]
  decide +kernel

theorem finish_spSafe (v : Ctr32Impl) :
    (finish v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finish, finPre, lastLen, Code.all, finalize_spSafe v]; decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

theorem absorb_correct (v : Ctr32Impl) (s : State) (hs : absorbX86_64.pre s) :
    ∃ t s', Exec isa (absorb v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ absorbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorb_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (absorb_mx v) he hg, hp⟩

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : finishX86_64.pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finish_mx v) he hg, hp⟩

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 16 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified X86_64.target (init v.expand v.callee v.suffix) (Spec.Cmac.aesInitContract X86_64.abi 16) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, initX86_64, X86_64.abi,
      X86_64.argRegs] [initSat] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified (v : Ctr32Impl) :
    Verified X86_64.target (absorb v.callee v.suffix) (Spec.Cmac.aesAbsorbContract X86_64.abi 16) :=
  Verified.of_correct (absorb_correct v) (absorb_ct v) (by
    sig_implies [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, absorbX86_64, X86_64.abi,
      X86_64.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x2000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified (v : Ctr32Impl) :
    Verified X86_64.target (finish v.callee v.suffix) (Spec.Cmac.aesFinishContract X86_64.abi 16) :=
  Verified.of_correct (finish_correct v) (finish_ct v) (by
    sig_implies [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, finishX86_64, X86_64.abi,
      X86_64.argRegs] [finishSat] using finishSat)

end VG.Proof.CmacAes.Stream.X86_64

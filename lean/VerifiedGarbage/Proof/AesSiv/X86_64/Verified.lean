import VerifiedGarbage.Proof.AesSiv.X86_64.Init
import VerifiedGarbage.Proof.AesSiv.X86_64.S2vStart
import VerifiedGarbage.Proof.AesSiv.X86_64.CryptCT
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Siv.Contract

/-!
# AES-SIV on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), a state satisfying each precondition, and the shared
contracts of `Spec/Siv/Contract.lean`, with 16 bytes of stack: the return
addresses of the call of a CMAC function (or of `vg_aes_ctr32`) and of its
call of `vg_aes_ctr32`.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (update_mx subkeys_mx finalize_mx update_spSafe subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs, v.expandMxcsr, subkeys_mx v]; decide +kernel

theorem s2vStart_mx (v : Ctr32Impl) : (s2vStart v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [s2vStart, callFinalize, Code.allInstrs, finalize_mx v]; decide +kernel

theorem s2vAd_mx (v : Ctr32Impl) : (s2vAd v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [s2vAd, cmacOf, cmacPre, callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v]
  decide +kernel

theorem seal_mx (v : Ctr32Impl) : («seal» v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», finish, shortTail, longTail, shortMac, longMac, copy, ctr, ctrBody, ctrMin, xorBytes, callUpdate,
    callFinalize, Code.allInstrs, update_mx v, finalize_mx v, v.mxcsr]
  decide +kernel

theorem open_mx (v : Ctr32Impl) : («open» v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», finish, shortTail, longTail, shortMac, longMac, copy, ctr, ctrBody, ctrMin, xorBytes, maskData,
    callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v, v.mxcsr]
  decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem s2vStart_spSafe (v : Ctr32Impl) : (s2vStart v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [s2vStart, callFinalize, Code.all, finalize_spSafe v]; decide +kernel

theorem s2vAd_spSafe (v : Ctr32Impl) : (s2vAd v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [s2vAd, cmacOf, cmacPre, callUpdate, callFinalize, Code.all, update_spSafe v, finalize_spSafe v]
  decide +kernel

theorem seal_spSafe (v : Ctr32Impl) : («seal» v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», finish, shortTail, longTail, shortMac, longMac, copy, ctr, ctrBody, ctrMin, xorBytes, callUpdate,
    callFinalize, Code.all, update_spSafe v, finalize_spSafe v, v.spSafe]
  decide +kernel

theorem open_spSafe (v : Ctr32Impl) : («open» v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», finish, shortTail, longTail, shortMac, longMac, copy, ctr, ctrBody, ctrMin, xorBytes, maskData,
    callUpdate, callFinalize, Code.all, update_spSafe v, finalize_spSafe v, v.spSafe]
  decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

theorem s2vStart_correct (v : Ctr32Impl) (s : State) (hs : s2vStartX86_64.pre s) :
    ∃ t s', Exec isa (s2vStart v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ s2vStartX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := s2v_start_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (s2vStart_mx v) he hg, hp⟩

theorem s2vAd_correct (v : Ctr32Impl) (s : State) (hs : s2vAdX86_64.pre s) :
    ∃ t s', Exec isa (s2vAd v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ s2vAdX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := s2v_ad_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (s2vAd_mx v) he hg, hp⟩

theorem seal_correct (v : Ctr32Impl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_correct (v : Ctr32Impl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified X86_64.target (init v.expand v.callee v.suffix) (Spec.Siv.initContract X86_64.abi 16) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Spec.Siv.initContract, Spec.Siv.initSig, initX86_64, X86_64.abi, X86_64.argRegs] [initSat]
      using initSat)

/-- A state satisfying `vg_aes_siv_s2v_start`'s precondition. -/
def startSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 512⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2560⟩]

theorem s2vStart_verified (v : Ctr32Impl) :
    Verified X86_64.target (s2vStart v.callee v.suffix) (Spec.Siv.s2vStartContract X86_64.abi 16) :=
  Verified.of_correct (s2vStart_correct v) (s2v_start_ct v) (by
    sig_implies [Spec.Siv.s2vStartContract, Spec.Siv.s2vStartSig, s2vStartX86_64, X86_64.abi, X86_64.argRegs]
      [startSat] using startSat)

/-- A state satisfying `vg_aes_siv_s2v_ad`'s precondition (with an empty string). -/
def adSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 512⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2560⟩]

theorem s2vAd_verified (v : Ctr32Impl) :
    Verified X86_64.target (s2vAd v.callee v.suffix) (Spec.Siv.s2vAdContract X86_64.abi 16) :=
  Verified.of_correct (s2vAd_correct v) (s2v_ad_ct v) (by
    sig_implies [Spec.Siv.s2vAdContract, Spec.Siv.s2vAdSig, s2vAdX86_64, X86_64.abi, X86_64.argRegs]
      [adSat] using adSat)

/-- A state satisfying the precondition of `vg_aes_siv_seal` and `vg_aes_siv_open` (with no data). -/
def cryptSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2560⟩]

theorem seal_verified (v : Ctr32Impl) :
    Verified X86_64.target («seal» v.callee v.suffix) (Spec.Siv.sealContract X86_64.abi 16) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Spec.Siv.sealContract, Spec.Siv.sealSig, sealX86_64, cryptPre, cryptPub, X86_64.abi,
      X86_64.argRegs] [cryptSat] using cryptSat)

theorem open_verified (v : Ctr32Impl) :
    Verified X86_64.target («open» v.callee v.suffix) (Spec.Siv.openContract X86_64.abi 16) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Spec.Siv.openContract, Spec.Siv.openSig, Spec.Siv.sealSig, openX86_64, cryptPre, cryptPub,
      X86_64.abi, X86_64.argRegs] [cryptSat] using cryptSat)

end VG.Proof.AesSiv.X86_64

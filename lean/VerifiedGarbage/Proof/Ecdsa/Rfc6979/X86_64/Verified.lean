import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on x86-64: `Verified`

For any implementation `v` of SHA-256's compression function: `sign_ok`
gives the contract's postcondition and keeps the callee-saved registers and
the return address; no instruction of the function or of those it calls
loads MXCSR (`sign_mx`: the HMAC functions' and the compression function's,
from what the variant and PBKDF2's proofs know of them, and `core`'s, from
its literal), so it is kept too (`abiPreserved`). Constant time up to the
number of candidates: `sign_ct`.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Pbkdf2.Md.X86_64 (core_hmacInit core_hmacFin core_updC)

variable (v : Compress)

theorem reduce_eq : (cfgOf v).reduce = cfgC.reduce := rfl
theorem initCnt_eq : (cfgOf v).initCnt = cfgC.initCnt := rfl
theorem B_eq : (cfgOf v).H.P.B = 64 := rfl
theorem coreC_eq : (cfgOf v).coreC = Impl.Ecdsa.X86_64.signP256 := rfl

/-- No instruction loads MXCSR: not those of the functions it calls, by what
the variant and the proofs of HMAC's functions know of them, nor its own,
which the kernel evaluates. -/
theorem sign_mx : (cfgOf v).sign.allInstrs (fun i => !loadsMxcsr i) = true := by
  have K := Proof.Pbkdf2.Md.X86_64.Sha256.callees v
  have C := Proof.Pbkdf2.Md.X86_64.Sha256.coreOK
  have hI : (cfgOf v).H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacInit K.cMx K.iMx C.hinitMx
  have hU : (cfgOf v).H.updC.allInstrs (fun i => !loadsMxcsr i) = true := core_updC K.cMx C.updMx
  have hF : (cfgOf v).H.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacFin K.cMx C.hfinMx
  have hK : Impl.Ecdsa.X86_64.signP256.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide
  simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs,
    reduce_eq, initCnt_eq, B_eq, coreC_eq, hI, hU, hF, hK, Bool.and_true, Bool.true_and]
  decide +kernel

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem sign_spSafe : (cfgOf v).sign.all (fun i => !isa.writesSp i) = true := by
  have K := Proof.Pbkdf2.Md.X86_64.Sha256.callees v
  have C := Proof.Pbkdf2.Md.X86_64.Sha256.coreOK
  have hI : (cfgOf v).H.hmacInit.allInstrs (fun i => !isa.writesSp i) = true := core_hmacInit K.cSp K.iSp C.hinitSp
  have hU₀ : Proof.Pbkdf2.Md.X86_64.Sha256.coreH.updC.allInstrs (fun i => !isa.writesSp i) = true := by
    decide +kernel
  have hU : (cfgOf v).H.updC.allInstrs (fun i => !isa.writesSp i) = true := core_updC K.cSp hU₀
  have hF : (cfgOf v).H.hmacFin.allInstrs (fun i => !isa.writesSp i) = true := core_hmacFin K.cSp C.hfinSp
  have hK : Impl.Ecdsa.X86_64.signP256.allInstrs (fun i => !isa.writesSp i) = true := by lit_decide
  refine Code.all_of_allInstrs ?_
  simp only [Cfg.sign, Cfg.body, Cfg.tryOne, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs,
    reduce_eq, initCnt_eq, B_eq, coreC_eq, hI, hU, hF, hK, Bool.and_true, Bool.true_and]
  decide +kernel

theorem sign_x86 (s : State) (h : rfcX86_64.pre s) :
    ∃ t s', Exec isa (cfgOf v).sign s t s' ∧ abiPreserved s s' ∧ rfcX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sign_ok (v := v) h
  exact ⟨t, s', he, abiPreserved_of_exec (sign_mx v) he hg, hp⟩

theorem sign_verified :
    Verified X86_64.target (cfgOf v).sign (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86_64.abi 160) :=
  Verified.of_correct (sign_x86 v) sign_ct implies

end VG.Proof.Ecdsa.Rfc6979.X86_64

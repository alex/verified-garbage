import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Layout
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# Ed448 verification on x86-64: the precondition and the layout

The precondition of `verifyContract X86_64.abi 272`, spelled out (`VPre`),
and the layout of a run from a state satisfying it (`vlay`), which is `Ok`
if the context is shorter than 256 bytes (`vlay_ok`).
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64

section
variable (s : State)

abbrev vPk : Region := ⟨s.gpr .rdi, 57⟩
abbrev vCtx : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
abbrev vMsg : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev vSig : Region := ⟨s.gpr .r9, 114⟩
abbrev vArgs : Region := ⟨stackArgAddr s 0, 8⟩
abbrev vScr : Region := ⟨stackArg s 0, 8192⟩
abbrev vRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev vStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 272, 272⟩

end

/-- The precondition of `verifyContract X86_64.abi 272`. -/
structure VPre (s : State) : Prop where
  sp : 272 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64
  rd : s.rd = [vPk s, vCtx s, vMsg s, vSig s, vArgs s]
  wr : s.wr = [vScr s]
  pkScr : (vPk s).Disjoint (vScr s)
  ctxScr : (vCtx s).Disjoint (vScr s)
  msgScr : (vMsg s).Disjoint (vScr s)
  sigScr : (vSig s).Disjoint (vScr s)
  scrArgs : (vScr s).Disjoint (vArgs s)
  retPk : (vRet s).Disjoint (vPk s)
  retCtx : (vRet s).Disjoint (vCtx s)
  retMsg : (vRet s).Disjoint (vMsg s)
  retSig : (vRet s).Disjoint (vSig s)
  retScr : (vRet s).Disjoint (vScr s)
  retArgs : (vRet s).Disjoint (vArgs s)
  stkPk : (vStk s).Disjoint (vPk s)
  stkCtx : (vStk s).Disjoint (vCtx s)
  stkMsg : (vStk s).Disjoint (vMsg s)
  stkSig : (vStk s).Disjoint (vSig s)
  stkScr : (vStk s).Disjoint (vScr s)
  stkArgs : (vStk s).Disjoint (vArgs s)
  nPk : (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64
  nCtx : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nMsg : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nSig : (s.gpr .r9).toNat + 114 ≤ 2 ^ 64
  nScr : (stackArg s 0).toNat + 8192 ≤ 2 ^ 64

theorem vPre_of {s : State} (h : (Spec.Ed448.verifyContract X86_64.abi 272).pre s) : VPre s := by
  sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs,
    List.range, List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, pkScr, ctxScr, msgScr, sigScr, scrArgs, retPk, retCtx, retMsg, retSig, retScr,
    retArgs, stkPk, stkCtx, stkMsg, stkSig, stkScr, stkArgs, nPk, nCtx, nMsg, nSig, nScr⟩ := h
  exact ⟨sp, sp2, rd, wr, pkScr, ctxScr, msgScr, sigScr, scrArgs, retPk, retCtx, retMsg, retSig, retScr,
    retArgs, stkPk, stkCtx, stkMsg, stkSig, stkScr, stkArgs, nPk, nCtx, nMsg, nSig, nScr⟩

/-- The layout of a run of `verify` from `s`. -/
def vlay (s : State) : Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 272
  pk := s.gpr .rdi
  ctx := s.gpr .rsi
  ctxLen := s.gpr .rdx
  msg := s.gpr .rcx
  len := s.gpr .r8
  sig := s.gpr .r9
  scr := stackArg s 0
  rd := s.rd
  wr := s.wr

theorem vlay_B (s : State) : (vlay s).B + BitVec.ofNat 64 272 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem vlay_ok {s : State} (h : VPre s) (h8 : (s.gpr .rdx).toNat < 256) : (vlay s).Ok := by
  have eR : (vlay s).RET = vRet s := by
    show (⟨(vlay s).B + BitVec.ofNat 64 272, 8⟩ : Region) = _
    rw [vlay_B]
  refine ⟨h8, ?_, h.wr, by simp [vlay, h.rd], by simp [vlay, h.rd], by simp [vlay, h.rd], by simp [vlay, h.rd],
    h.pkScr.symm, h.sigScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr, h.stkPk, h.stkSig, h.stkMsg, h.stkCtx,
    by rw [eR]; exact h.retScr, h.nPk, h.nSig, h.nMsg, h.nCtx, h.nScr⟩
  have := h.sp; have := h.sp2
  simp only [vlay, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end VG.Proof.Ed448.X86_64.Verify

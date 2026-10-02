import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignPre

/-!
# ML-DSA on x86-64, `verify_message`: the precondition and the layout

Untrusted: everything here is checked by Lean. The precondition of
`verifyMessageContract p X86_64.abi 112`, spelled out (`VPre`), and the
layout of a run from a state satisfying it (`vlay`): the key is `pk`, there
is no `rnd` (its slot holds 0) and `scratch` is the only argument on the
stack.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s : State)

abbrev vPk : Region := ⟨s.gpr .rdi, p.pkLen⟩
abbrev vSigR : Region := ⟨s.gpr .r9, p.sigLen⟩
abbrev vArgs : Region := ⟨stackArgAddr s 0, 8⟩
abbrev vScr : Region := ⟨stackArg s 0, mScrLen p⟩

end

/-- The precondition of `verifyMessageContract p X86_64.abi 112`. -/
structure VPre (p : Params) (s : State) : Prop where
  sp : 112 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64
  rd : s.rd = [vPk p s, rMsg s, rCtx s, vSigR p s, vArgs s]
  wr : s.wr = [vScr p s]
  pkScr : (vPk p s).Disjoint (vScr p s)
  msgScr : (rMsg s).Disjoint (vScr p s)
  ctxScr : (rCtx s).Disjoint (vScr p s)
  sigScr : (vSigR p s).Disjoint (vScr p s)
  scrArgs : (vScr p s).Disjoint (vArgs s)
  retPk : (rRet s).Disjoint (vPk p s)
  retMsg : (rRet s).Disjoint (rMsg s)
  retCtx : (rRet s).Disjoint (rCtx s)
  retSig : (rRet s).Disjoint (vSigR p s)
  retScr : (rRet s).Disjoint (vScr p s)
  retArgs : (rRet s).Disjoint (vArgs s)
  stkPk : (rStk s).Disjoint (vPk p s)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkSig : (rStk s).Disjoint (vSigR p s)
  stkScr : (rStk s).Disjoint (vScr p s)
  stkArgs : (rStk s).Disjoint (vArgs s)
  nPk : (s.gpr .rdi).toNat + p.pkLen ≤ 2 ^ 64
  nMsg : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nSig : (s.gpr .r9).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (stackArg s 0).toNat + mScrLen p ≤ 2 ^ 64

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageContract p X86_64.abi 112).pre s) : VPre p s := by
  sig_pre [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrArgs, retPk, retMsg, retCtx, retSig, retScr,
    retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkArgs, nPk, nMsg, nCtx, nSig, nScr⟩ := h
  exact ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrArgs, retPk, retMsg, retCtx, retSig, retScr,
    retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkArgs, nPk, nMsg, nCtx, nSig, nScr⟩

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 31 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The layout of a run of `verify_message` from `s`. -/
def vlay (p : Params) (s : State) : Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 112
  key := s.gpr .rdi
  keyLen := p.pkLen
  msg := s.gpr .rsi
  len := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  rnd := 0
  sig := s.gpr .r9
  scr := stackArg s 0
  E := oE p
  rd := s.rd
  wr := s.wr

theorem vlay_B (p : Params) (s : State) :
    (vlay p s).B + BitVec.ofNat 64 112 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem vlay_X (p : Params) (s : State) : Within (vlay p s).XS (vScr p s) :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem vlay_ok {p : Params} (hp : p ∈ params) {s : State} (h : VPre p s) (h8 : (s.gpr .r8).toNat < 256) :
    (vlay p s).Ok := by
  have hX := vlay_X p s
  have hXs := hX.sub
  refine ⟨h8, oE_lt hp, pkLen_ge hp, ?_, ⟨vScr p s, by simp [vlay, h.wr], hX⟩, by simp [vlay, h.rd],
    by simp [vlay, h.rd], by simp [vlay, h.rd], h.pkScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs,
    h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs, h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx, ?_⟩
  · have := h.sp; have := (s.gpr .rsp).isLt
    simp only [vlay, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · intro R hR
    simp only [vlay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
    have := h.nScr
    subst hR; simp only; omega

theorem vmu_eq (p : Params) (s : State) :
    (vlay p s).MU = stackArg s 0 + BitVec.ofNat 64 (oE p + 840) := by
  simp only [Lay.MU, Lay.X, vlay, add_add]

theorem vmu_nowrap {p : Params} {s : State} (h : VPre p s) : (vlay p s).MU.toNat + 64 ≤ 2 ^ 64 := by
  have hn : (stackArg s 0).toNat + (oE p + 1024) ≤ 2 ^ 64 := by rw [← mScr_eq]; exact h.nScr
  rw [vmu_eq]
  generalize oE p = e at hn ⊢
  generalize stackArg s 0 = x at hn ⊢
  clear h
  rw [toNat_add_ofNat (by omega), Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left (by clear hn; omega) _) hn

end VG.Proof.MlDsa.X86_64.Message

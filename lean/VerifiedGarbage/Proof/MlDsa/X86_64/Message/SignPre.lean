import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# ML-DSA on x86-64, `sign_message`: the precondition and the layout

Untrusted: everything here is checked by Lean. The precondition of
`signMessageContract p X86_64.abi 112`, spelled out (`SPre`), and the layout
of a run from a state satisfying it (`slay`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

section
variable (p : Params) (s : State)

abbrev rSk : Region := ⟨s.gpr .rdi, p.skLen⟩
abbrev rMsg : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
abbrev rCtx : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev rRnd : Region := ⟨s.gpr .r9, 32⟩
abbrev rArgs : Region := ⟨stackArgAddr s 0, 16⟩
abbrev rSig : Region := ⟨stackArg s 0, p.sigLen⟩
abbrev rScr : Region := ⟨stackArg s 1, mScrLen p⟩
abbrev rRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev rStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 112, 112⟩

end

/-- The precondition of `signMessageContract p X86_64.abi 112`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 112 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [rSk p s, rMsg s, rCtx s, rRnd s, rArgs s]
  wr : s.wr = [rSig p s, rScr p s]
  skSig : (rSk p s).Disjoint (rSig p s)
  skScr : (rSk p s).Disjoint (rScr p s)
  msgSig : (rMsg s).Disjoint (rSig p s)
  msgScr : (rMsg s).Disjoint (rScr p s)
  ctxSig : (rCtx s).Disjoint (rSig p s)
  ctxScr : (rCtx s).Disjoint (rScr p s)
  rndSig : (rRnd s).Disjoint (rSig p s)
  rndScr : (rRnd s).Disjoint (rScr p s)
  sigScr : (rSig p s).Disjoint (rScr p s)
  sigArgs : (rSig p s).Disjoint (rArgs s)
  scrArgs : (rScr p s).Disjoint (rArgs s)
  retSk : (rRet s).Disjoint (rSk p s)
  retMsg : (rRet s).Disjoint (rMsg s)
  retCtx : (rRet s).Disjoint (rCtx s)
  retRnd : (rRet s).Disjoint (rRnd s)
  retSig : (rRet s).Disjoint (rSig p s)
  retScr : (rRet s).Disjoint (rScr p s)
  retArgs : (rRet s).Disjoint (rArgs s)
  stkSk : (rStk s).Disjoint (rSk p s)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkRnd : (rStk s).Disjoint (rRnd s)
  stkSig : (rStk s).Disjoint (rSig p s)
  stkScr : (rStk s).Disjoint (rScr p s)
  stkArgs : (rStk s).Disjoint (rArgs s)
  nSk : (s.gpr .rdi).toNat + p.skLen ≤ 2 ^ 64
  nMsg : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nRnd : (s.gpr .r9).toNat + 32 ≤ 2 ^ 64
  nSig : (stackArg s 0).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (stackArg s 1).toNat + mScrLen p ≤ 2 ^ 64

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p X86_64.abi 112).pre s) : SPre p s := by
  sig_pre [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, skSig, skScr, msgSig, msgScr, ctxSig, ctxScr, rndSig, rndScr, sigScr, sigArgs,
    scrArgs, retSk, retMsg, retCtx, retRnd, retSig, retScr, retArgs, stkSk, stkMsg, stkCtx, stkRnd, stkSig,
    stkScr, stkArgs, nSk, nMsg, nCtx, nRnd, nSig, nScr⟩ := h
  exact ⟨sp, sp2, rd, wr, skSig, skScr, msgSig, msgScr, ctxSig, ctxScr, rndSig, rndScr, sigScr, sigArgs,
    scrArgs, retSk, retMsg, retCtx, retRnd, retSig, retScr, retArgs, stkSk, stkMsg, stkCtx, stkRnd, stkSig,
    stkScr, stkArgs, nSk, nMsg, nCtx, nRnd, nSig, nScr⟩

/-! ## The layout -/

theorem mScr_eq (p : Params) : mScrLen p = oE p + 1024 := by
  simp only [mScrLen, messageScratchWords, oE]; omega

theorem oE_lt {p : Params} (hp : p ∈ params) : oE p + 1024 < 2 ^ 31 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem skLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 31 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 112
  key := s.gpr .rdi
  keyLen := p.skLen
  msg := s.gpr .rsi
  len := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  rnd := s.gpr .r9
  sig := stackArg s 0
  scr := stackArg s 1
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_B (p : Params) (s : State) :
    (slay p s).B + BitVec.ofNat 64 112 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem slay_X (p : Params) (s : State) : Within (slay p s).XS (rScr p s) :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem slay_ok {p : Params} (hp : p ∈ params) {s : State} (h : SPre p s) (h8 : (s.gpr .r8).toNat < 256) :
    (slay p s).Ok := by
  have hX := slay_X p s
  have hXs := hX.sub
  refine ⟨h8, oE_lt hp, skLen_ge hp, ?_, ⟨rScr p s, by simp [slay, h.wr], hX⟩, by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.skScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs,
    h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs, h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx, ?_⟩
  · have := h.sp; have := (s.gpr .rsp).isLt
    simp only [slay, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · intro R hR
    simp only [slay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
    have := h.nSig; have := h.nScr
    rcases hR with rfl | rfl <;> simp only <;> omega

theorem mu_eq (p : Params) (s : State) :
    (slay p s).MU = stackArg s 1 + BitVec.ofNat 64 (oE p + 840) := by
  simp only [Lay.MU, Lay.X, slay, add_add]


theorem mu_nowrap {p : Params} {s : State} (h : SPre p s) : (slay p s).MU.toNat + 64 ≤ 2 ^ 64 := by
  have hn : (stackArg s 1).toNat + (oE p + 1024) ≤ 2 ^ 64 := by rw [← mScr_eq]; exact h.nScr
  rw [mu_eq]
  generalize oE p = e at hn ⊢
  generalize stackArg s 1 = x at hn ⊢
  clear h
  rw [toNat_add_ofNat (by omega), Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left (by clear hn; omega) _) hn


end VG.Proof.MlDsa.X86_64.Message

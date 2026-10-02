import VerifiedGarbage.Proof.MlDsa.Arm.Message.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.TCB.Arm.Target

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The preconditions of
`signMessageContract p Arm.abi 36` and `verifyMessageContract p Arm.abi
36`, spelled out (`SPre`, `VPre`), and the layouts of runs from states
satisfying them (`slay`, `vlay`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

theorem mScr_eq (p : Params) : mScrLen p = oE p + 1024 := by
  simp only [mScrLen, messageScratchWords, oE]; omega

theorem oE_lt {p : Params} (hp : p ∈ params) : oE p + 1024 < 2 ^ 31 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem skLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

section
variable (s : State)

abbrev rKey (n : Nat) : Region := ⟨State.addr (s.gpr .r0), n⟩
abbrev rMsg : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
abbrev rCtx : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
/-- The `n` bytes below the stack pointer the calls use. -/
abbrev rStk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 36, 36⟩
/-- The arguments on the stack. -/
abbrev rArgs (n : Nat) : Region := ⟨stackArgAddr s 0, n⟩
/-- The `j`-th argument on the stack, as an address. -/
abbrev sArg (j : Nat) : Addr := State.addr (stackArg s j)

end

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

/-! ## Signing -/

/-- The precondition of `signMessageContract p Arm.abi 36`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 36 ≤ s.sp.toNat
  spA : s.sp.toNat + 16 ≤ 2 ^ 32
  rd : s.rd = [rKey s p.skLen, rMsg s, rCtx s, ⟨sArg s 1, 32⟩, rArgs s 16]
  wr : s.wr = [⟨sArg s 2, p.sigLen⟩, ⟨sArg s 3, mScrLen p⟩]
  skSig : (rKey s p.skLen).Disjoint ⟨sArg s 2, p.sigLen⟩
  skScr : (rKey s p.skLen).Disjoint ⟨sArg s 3, mScrLen p⟩
  msgSig : (rMsg s).Disjoint ⟨sArg s 2, p.sigLen⟩
  msgScr : (rMsg s).Disjoint ⟨sArg s 3, mScrLen p⟩
  ctxSig : (rCtx s).Disjoint ⟨sArg s 2, p.sigLen⟩
  ctxScr : (rCtx s).Disjoint ⟨sArg s 3, mScrLen p⟩
  rndSig : Region.Disjoint ⟨sArg s 1, 32⟩ ⟨sArg s 2, p.sigLen⟩
  rndScr : Region.Disjoint ⟨sArg s 1, 32⟩ ⟨sArg s 3, mScrLen p⟩
  sigScr : Region.Disjoint ⟨sArg s 2, p.sigLen⟩ ⟨sArg s 3, mScrLen p⟩
  sigArgs : Region.Disjoint ⟨sArg s 2, p.sigLen⟩ (rArgs s 16)
  scrArgs : Region.Disjoint ⟨sArg s 3, mScrLen p⟩ (rArgs s 16)
  stkSk : (rStk s).Disjoint (rKey s p.skLen)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkRnd : (rStk s).Disjoint ⟨sArg s 1, 32⟩
  stkSig : (rStk s).Disjoint ⟨sArg s 2, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨sArg s 3, mScrLen p⟩
  stkArgs : (rStk s).Disjoint (rArgs s 16)
  nSk : (s.gpr .r0).toNat + p.skLen ≤ 2 ^ 32
  nMsg : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  nCtx : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nRnd : (stackArg s 1).toNat + 32 ≤ 2 ^ 32
  nSig : (stackArg s 2).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (stackArg s 3).toNat + mScrLen p ≤ 2 ^ 32

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p Arm.abi 36).pre s) : SPre p s := by
  sig_pre [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24, a25, h⟩ := h
  obtain ⟨a26, a27, a28⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28⟩

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .r0
  keyLen := p.skLen
  msg := s.gpr .r1
  len := s.gpr .r2
  ctx := s.gpr .r3
  ctxLen := stackArg s 0
  rnd := stackArg s 1
  sig := stackArg s 2
  scr := stackArg s 3
  scrLen := mScrLen p
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_ok {p : Params} (hp : p ∈ params) {s : State} (h : SPre p s) (h8 : (stackArg s 0).toNat < 256) :
    (slay p s).Ok :=
  ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], skLen_ge hp, h.sp, h.nScr, by simp [slay, h.wr], by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.skScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr,
    h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx⟩

/-! ## Verification -/

/-- The precondition of `verifyMessageContract p Arm.abi 36`. -/
structure VPre (p : Params) (s : State) : Prop where
  sp : 36 ≤ s.sp.toNat
  spA : s.sp.toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [rKey s p.pkLen, rMsg s, rCtx s, ⟨sArg s 1, p.sigLen⟩, rArgs s 12]
  wr : s.wr = [⟨sArg s 2, mScrLen p⟩]
  pkScr : (rKey s p.pkLen).Disjoint ⟨sArg s 2, mScrLen p⟩
  msgScr : (rMsg s).Disjoint ⟨sArg s 2, mScrLen p⟩
  ctxScr : (rCtx s).Disjoint ⟨sArg s 2, mScrLen p⟩
  sigScr : Region.Disjoint ⟨sArg s 1, p.sigLen⟩ ⟨sArg s 2, mScrLen p⟩
  scrArgs : Region.Disjoint ⟨sArg s 2, mScrLen p⟩ (rArgs s 12)
  stkPk : (rStk s).Disjoint (rKey s p.pkLen)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkSig : (rStk s).Disjoint ⟨sArg s 1, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨sArg s 2, mScrLen p⟩
  stkArgs : (rStk s).Disjoint (rArgs s 12)
  nPk : (s.gpr .r0).toNat + p.pkLen ≤ 2 ^ 32
  nMsg : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  nCtx : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nSig : (stackArg s 1).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (stackArg s 2).toNat + mScrLen p ≤ 2 ^ 32

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageContract p Arm.abi 36).pre s) : VPre p s := by
  sig_pre [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩

/-- The layout of a run of `verify_message` from `s` (`sig` in the slot of `rnd` too). -/
def vlay (p : Params) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .r0
  keyLen := p.pkLen
  msg := s.gpr .r1
  len := s.gpr .r2
  ctx := s.gpr .r3
  ctxLen := stackArg s 0
  rnd := stackArg s 1
  sig := stackArg s 1
  scr := stackArg s 2
  scrLen := mScrLen p
  E := oE p
  rd := s.rd
  wr := s.wr

theorem vlay_ok {p : Params} (hp : p ∈ params) {s : State} (h : VPre p s) (h8 : (stackArg s 0).toNat < 256) :
    (vlay p s).Ok :=
  ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], pkLen_ge hp, h.sp, h.nScr, by simp [vlay, h.wr], by simp [vlay, h.rd],
    by simp [vlay, h.rd], by simp [vlay, h.rd], h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr,
    h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx⟩

end VG.Proof.MlDsa.Arm.Message

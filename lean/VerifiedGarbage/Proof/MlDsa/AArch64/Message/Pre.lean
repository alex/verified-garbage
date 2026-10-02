import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The preconditions of
`signMessageContract p AArch64.abi 16` and `verifyMessageContract p
AArch64.abi 16`, spelled out (`SPre`, `VPre`), and the layouts of runs from
states satisfying them (`slay`, `vlay`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
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

section
variable (p : Params) (s : State)

abbrev rKey (n : Nat) : Region := ⟨s.gpr .x0, n⟩
abbrev rMsg : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
abbrev rCtx : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
abbrev rStk : Region := ⟨s.sp - 16#64, 16⟩

end

/-! ## Signing -/

/-- The precondition of `signMessageContract p AArch64.abi 16`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [rKey s p.skLen, rMsg s, rCtx s, ⟨s.gpr .x5, 32⟩]
  wr : s.wr = [⟨s.gpr .x6, p.sigLen⟩, ⟨s.gpr .x7, mScrLen p⟩]
  skSig : (rKey s p.skLen).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  skScr : (rKey s p.skLen).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  msgSig : (rMsg s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  msgScr : (rMsg s).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  ctxSig : (rCtx s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  ctxScr : (rCtx s).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  rndSig : Region.Disjoint ⟨s.gpr .x5, 32⟩ ⟨s.gpr .x6, p.sigLen⟩
  rndScr : Region.Disjoint ⟨s.gpr .x5, 32⟩ ⟨s.gpr .x7, mScrLen p⟩
  sigScr : Region.Disjoint ⟨s.gpr .x6, p.sigLen⟩ ⟨s.gpr .x7, mScrLen p⟩
  stkSk : (rStk s).Disjoint (rKey s p.skLen)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkRnd : (rStk s).Disjoint ⟨s.gpr .x5, 32⟩
  stkSig : (rStk s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  nSk : (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  nRnd : (s.gpr .x5).toNat + 32 ≤ 2 ^ 64
  nSig : (s.gpr .x6).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (s.gpr .x7).toNat + mScrLen p ≤ 2 ^ 64

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p AArch64.abi 16).pre s) : SPre p s := by
  sig_pre [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24⟩

theorem skLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .x0
  keyLen := p.skLen
  msg := s.gpr .x1
  len := s.gpr .x2
  ctx := s.gpr .x3
  ctxLen := s.gpr .x4
  rnd := s.gpr .x5
  sig := s.gpr .x6
  scr := s.gpr .x7
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_X (p : Params) (s : State) : Within (slay p s).XS ⟨s.gpr .x7, mScrLen p⟩ :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem toNat_X {scr : Addr} {e n : Nat} (h : scr.toNat + n ≤ 2 ^ 64) (he : e + 1024 ≤ n) :
    (scr + BitVec.ofNat 64 e).toNat + 1024 ≤ 2 ^ 64 := by
  rw [toNat_add_ofNat (by omega)]; omega

theorem slay_ok {p : Params} (hp : p ∈ params) {s : State} (h : SPre p s) (h8 : (s.gpr .x4).toNat < 256) :
    (slay p s).Ok := by
  have hX := slay_X p s
  have hXs := hX.sub
  have hE := oE_lt hp
  refine ⟨h8, hE, skLen_ge hp, h.sp, toNat_X (e := oE p) h.nScr (by rw [mScr_eq]),
    ⟨_, by simp [slay, h.wr], hX⟩, by simp [slay, h.rd], by simp [slay, h.rd], by simp [slay, h.rd],
    h.skScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs, h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs,
    h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx, ?_⟩
  intro R hR
  simp only [slay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
  have := h.nSig; have := h.nScr
  rcases hR with rfl | rfl <;> simp only <;> omega

/-! ## Verification -/

/-- The precondition of `verifyMessageContract p AArch64.abi 16`. -/
structure VPre (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [rKey s p.pkLen, rMsg s, rCtx s, ⟨s.gpr .x5, p.sigLen⟩]
  wr : s.wr = [⟨s.gpr .x6, mScrLen p⟩]
  pkScr : (rKey s p.pkLen).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  msgScr : (rMsg s).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  ctxScr : (rCtx s).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  sigScr : Region.Disjoint ⟨s.gpr .x5, p.sigLen⟩ ⟨s.gpr .x6, mScrLen p⟩
  stkPk : (rStk s).Disjoint (rKey s p.pkLen)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkSig : (rStk s).Disjoint ⟨s.gpr .x5, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  nPk : (s.gpr .x0).toNat + p.pkLen ≤ 2 ^ 64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  nSig : (s.gpr .x5).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (s.gpr .x6).toNat + mScrLen p ≤ 2 ^ 64

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageContract p AArch64.abi 16).pre s) : VPre p s := by
  sig_pre [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, a16, a17⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

/-- The layout of a run of `verify_message` from `s` (`sig` in the slot of `rnd` too). -/
def vlay (p : Params) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .x0
  keyLen := p.pkLen
  msg := s.gpr .x1
  len := s.gpr .x2
  ctx := s.gpr .x3
  ctxLen := s.gpr .x4
  rnd := s.gpr .x5
  sig := s.gpr .x5
  scr := s.gpr .x6
  E := oE p
  rd := s.rd
  wr := s.wr

theorem vlay_X (p : Params) (s : State) : Within (vlay p s).XS ⟨s.gpr .x6, mScrLen p⟩ :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem vlay_ok {p : Params} (hp : p ∈ params) {s : State} (h : VPre p s) (h8 : (s.gpr .x4).toNat < 256) :
    (vlay p s).Ok := by
  have hX := vlay_X p s
  have hXs := hX.sub
  have hE := oE_lt hp
  refine ⟨h8, hE, pkLen_ge hp, h.sp, toNat_X (e := oE p) h.nScr (by rw [mScr_eq]),
    ⟨_, by simp [vlay, h.wr], hX⟩, by simp [vlay, h.rd], by simp [vlay, h.rd], by simp [vlay, h.rd],
    h.pkScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs, h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs,
    h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx, ?_⟩
  intro R hR
  simp only [vlay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
  have := h.nScr
  subst hR; simp only; omega

end VG.Proof.MlDsa.AArch64.Message

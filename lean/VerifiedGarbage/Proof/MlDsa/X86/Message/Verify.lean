import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall

/-!
# ML-DSA on x86 (32-bit), `verify_message`: correct and constant time

Untrusted: everything here is checked by Lean. The body past the entry:
`tr = H(pk, 64)`, then `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, then the call
of the verification function on it (`verifyRest_piece`); in the leaf, after
the check (`verifyMessage_piece`); and what that says of the contract's
postcondition (`verifyMessage_verified`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece P0 E0 frameR retR LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

section
variable {p : Params}

theorem H_length (s : List Byte) (n : Nat) : (H s n).length = n :=
  Proof.Sha3.length_squeeze (by decide) (by decide) _ _

/-- `tr`, then `μ`, then the call of the verification function on it. -/
theorem verifyRest_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : VerifyFn p f)
    {ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) :
    Piece (VPre p) (VPub p) (CtxO (vlay p)) (fun s₀ s => LeafEnd s₀ (vW p s₀) s ∧ VB p s₀ s)
      (.seq (trHash p) (.seq (muHash (.off oMU)) (.seq (.block (setArgs verifyArgs)) (Impl.MlKem.X86.callRet rs4 n f)))) := by
  refine Piece.seq (trHash_piece (vShape hp).pubL (fun _ _ _ h => h) (fun _ _ => by show 5 ≤ 7; decide)
    (fun _ _ => rfl) tt₁ tt₂) (Piece.seq ((muHash_piece (lay := vlay p) (.off oMU)
    (fun s₀ => (vlay p s₀).X32 + BitVec.ofNat 32 840) (fun s₀ => H (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) 64)
    (by taint_decide) (vShape hp).pubL (fun _ _ _ h => h.1) (fun _ _ => by show 5 ≤ 7; decide) (fun _ _ => rfl) rfl
    (fun s₀ s h₀ hc => hc.ctx.off 840) (fun s₀ s₀' h₀ h₀' hq => by rw [((vShape hp).pubL s₀ s₀' h₀ h₀' hq).x])
    (fun s₀ s h₀ h => ?_) (fun _ _ => H_length _ _) (fun s₀ h₀ hL => ?_)).mono
    (fun _ _ _ h => h) fun s₀ s h₀ ⟨hc, hm⟩ => ⟨hc, ?_⟩) (verifyCall_piece hp hf))
  · rw [mu_eq h.1.ok, h.2]
    simp only [keyB]
    rw [p0_bytes (a := (vlay p s₀).key.setWidth 64) (n := (vlay p s₀).keyLen) (by decide) h₀.sp h₀.kPk
      (by show p.pkLen ≤ _; have := h₀.nPk; omega)]
    rfl
  · have hX := hL.x32_lt
    refine ⟨by rw [hL.x32_toNat (by omega)]; omega, by rw [mu_eq hL]; exact cov_x hL (e := 840) (k := 64) (by omega),
      by rw [mu_eq hL]; exact st_mu.symm, by rw [mu_eq hL]; exact mu_ks, by rw [mu_eq hL]; exact k_mu hL⟩
  · rw [hm]
    simp only [ctxB, msgB]
    rw [p0_bytes (a := (vlay p s₀).ctx.setWidth 64) (n := (vlay p s₀).ctxLen.toNat) (by decide) h₀.sp h₀.kCtx
        (by have := (arg s₀ 4).isLt; show (arg s₀ 4).toNat ≤ _; omega),
      p0_bytes (a := (vlay p s₀).msg.setWidth 64) (n := (vlay p s₀).len.toNat) (by decide) h₀.sp h₀.kMsg
        (by have := (arg s₀ 2).isLt; show (arg s₀ 2).toNat ≤ _; omega)]
    rfl

/-- What `verify_message` changes is apart from its frame and return address. -/
theorem verify_hW : ∀ s₀, VPre p s₀ → ∀ r ∈ vW p s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro s₀ h₀ r hr
  have hsp := h₀.sp
  have fr : Region.Sub (frameR s₀) (sStk s₀ 132) := by rw [stk_eq hsp]; exact below_sub (by decide) hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨h₀.kScr.sub_left fr, h₀.rScr⟩
  · exact ⟨Proof.MlKem.X86.Top.below_adj (sp := s₀.gpr .esp) (a := 16) (b := 132 - 16) (by omega),
      (Proof.MlKem.X86.Top.ret_below hsp).sub_right (below_inner (a := 132 - 16) (k := 16) (by omega) hsp)⟩

/-- `verify_message`, in its leaf. -/
theorem verifyMessage_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : VerifyFn p f)
    {ht ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) (htr : NoSp (trHash p)) :
    Piece (VPre p) (VPub p) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ VB p s₀ s) s₀ s') (verifyMessage n f p) :=
  top_piece (vShape hp) tt (vW p) verify_hW
    (nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_ite (NoSp.of_all (by decide +kernel))
      (nosp_seq (enter_nosp 6 p) (nosp_seq htr (nosp_seq (NoSp.of_all (by decide +kernel))
        (nosp_seq (NoSp.of_all (by decide +kernel)) (callRet_nosp hf.nosp)))))))
    (verifyRest_piece hp hf tt₁ tt₂)

/-- Memory with the arguments `0`, `0x2000`, `0`, `0x2000`, `0`, `0x3000` and
`0x10000` at `0x5004`. -/
def satMemV : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else
  if a = 0x501e then 1 else 0

/-- A state satisfying the precondition of `verify_message`. -/
def verifySat (p : Params) : State :=
  Proof.MlKem.X86.satState satMemV [⟨0, p.pkLen⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩]
    [⟨0x10000, mScrLen p⟩, ⟨0x5004, 28⟩]

theorem verifyMessage_verified (hp : p ∈ params) {n : String} {f : Prog isa} (hf : VerifyFn p f)
    {ht ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) (htr : NoSp (trHash p)) :
    Verified X86.target (verifyMessage n f p) (verifyMessageContract p X86.abi 132) := by
  refine Piece.verified (((verifyMessage_piece hp hf tt tt₁ tt₂ htr).pre_mono (fun _ h => vPre_of h)
    fun _ _ _ _ h => vpub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hB, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [Proof.MlKem.X86.setWidth_append32, hax]
    rcases hB with ⟨h8, h2⟩ | ⟨h8, hout⟩
    · rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; exact h8)]; exact h2
    · rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [verifyInternal, messageRep, pkTr, Proof.MlKem.bytesAt_length]
      simp only [vMu, hdrBytes, vlay, List.append_assoc] at hout
      simp only [List.append_assoc]
      exact hout
  · simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨verifySat mlDsa44, by sig_sat_check [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, verifySat, Proof.MlKem.X86.satState, satMemV]⟩
    · exact ⟨verifySat mlDsa65, by sig_sat_check [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, verifySat, Proof.MlKem.X86.satState, satMemV]⟩
    · exact ⟨verifySat mlDsa87, by sig_sat_check [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, verifySat, Proof.MlKem.X86.satState, satMemV]⟩

end

end VG.Proof.MlDsa.X86.Message

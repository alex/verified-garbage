import VerifiedGarbage.Proof.MlDsa.X86.Message.SignCall

/-!
# ML-DSA on x86 (32-bit), `sign_message`: correct and constant time

Untrusted: everything here is checked by Lean. The body past the entry:
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for `tr` the 64 bytes of `sk` at
64, then the call of the signing function on it (`signRest_piece`); in the
leaf, after the check (`signMessage_piece`); and what that says of the
contract's postcondition (`signMessage_post`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece P0 E0 frameR retR LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

section
variable {p : Params}

/-- Bytes apart from the stack the contract gives, as on entry, after the leaf's push. -/
theorem p0_bytes {s₀ : State} {N : Nat} (hN : 16 ≤ N) (hN' : N ≤ (s₀.gpr .esp).toNat) {a : Addr} {n : Nat}
    (hk : (sStk s₀ N).Disjoint ⟨a, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt (P0 s₀).mem a n = bytesAt s₀.mem a n := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by show 16 ≤ _; omega)
  exact Proof.MlKem.bytesAt_congr fun _ hi => hf.bytes (R := ⟨a, n⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((stk_eq hN' ▸ hk).sub_left (below_sub hN hN')).symm) hn hi

/-- `μ` is the message representative of the formatted message. -/
theorem sMu_eq {s₀ : State} (h₀ : SPre p s₀) (hk : 128 ≤ p.skLen) :
    messageRep (skTr (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen))
      ([0, BitVec.ofNat 8 (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat).length] ++
        bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++
        bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat) = sMu p s₀ := by
  have := h₀.nSk
  simp only [messageRep, skTr, Proof.MlKem.bytesAt_length]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]
  simp only [sMu, hdrBytes, slay, List.append_assoc]
  rw [Proof.MlKem.X86.ea_off (by omega)]

/-- `μ`, then the call of the signing function on it. -/
theorem signRest_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : SignFn p f) :
    Piece (SPre p) (SPub p) (CtxO (slay p)) (fun s₀ s => LeafEnd s₀ (sW p s₀) s ∧ SB p s₀ s)
      (.seq (muHash (.argOff 0 64)) (.seq (.block (setArgs signArgs)) (Impl.MlKem.X86.callRet rs5 n f))) := by
  have hk := skLen_ge hp
  refine Piece.seq ((muHash_piece (lay := slay p) (.argOff 0 64) (fun s₀ => arg s₀ 0 + BitVec.ofNat 32 64)
    (fun s₀ => bytesAt s₀.mem ((arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64) 64) (by taint_decide) (sShape hp).pubL
    (fun _ _ _ h => h) (fun _ _ => by show 5 ≤ 8; decide) (fun _ _ => rfl) rfl
    (fun s₀ s h₀ hc => hc.ctx.argOffV (by show 0 < 8; decide) 64)
    (fun s₀ s₀' h₀ h₀' hq => by rw [hq.args 0 (by decide)])
    (fun s₀ s h₀ hc => ?_) (fun _ _ => Proof.MlKem.bytesAt_length _ _ _) (fun s₀ h₀ hL => ?_)).mono
    (fun _ _ _ h => h) fun s₀ s h₀ ⟨hc, hm⟩ => ⟨hc, ?_⟩) (signCall_piece hp hf)
  · have hL := hc.ok
    have := h₀.nSk
    have wtr : Within ⟨(arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64, 64⟩ (slay p s₀).KEY := by
      rw [Proof.MlKem.X86.ea_off (by omega)]; exact within_off _ (show 64 + 64 ≤ p.skLen by omega)
    rw [hc.ctx.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide)]
    exact p0_bytes (by decide) h₀.sp (h₀.kSk.sub_right wtr.sub) (by decide)
  · have := h₀.nSk
    have wtr : Within ⟨(arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64, 64⟩ (slay p s₀).KEY := by
      rw [Proof.MlKem.X86.ea_off (by omega)]; exact within_off _ (show 64 + 64 ≤ p.skLen by omega)
    have hst : Region.Sub ⟨(slay p s₀).ST, 200⟩ (slay p s₀).SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega)
      simpa only [x0] using this
    refine ⟨?_, ⟨_, List.mem_append_left _ hL.inKey, wtr⟩, (hL.xKey.symm.sub_left wtr.sub).sub_right hst,
      (hL.xKey.symm.sub_left wtr.sub).sub_right (hL.sub_sc (by omega : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right wtr.sub⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hm]
    simp only [ctxB, msgB]
    rw [p0_bytes (a := (slay p s₀).ctx.setWidth 64) (n := (slay p s₀).ctxLen.toNat) (by decide) h₀.sp h₀.kCtx
        (by have := (arg s₀ 4).isLt; show (arg s₀ 4).toNat ≤ _; omega),
      p0_bytes (a := (slay p s₀).msg.setWidth 64) (n := (slay p s₀).len.toNat) (by decide) h₀.sp h₀.kMsg
        (by have := (arg s₀ 2).isLt; show (arg s₀ 2).toNat ≤ _; omega)]
    rfl


/-- What `sign_message` changes is apart from its frame and return address. -/
theorem sign_hW : ∀ s₀, SPre p s₀ → ∀ r ∈ sW p s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro s₀ h₀ r hr
  have hsp := h₀.sp
  have fr : Region.Sub (frameR s₀) (sStk s₀ 136) := by rw [stk_eq hsp]; exact below_sub (by decide) hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨h₀.kScr.sub_left fr, h₀.rScr⟩
  · exact ⟨Proof.MlKem.X86.Top.below_adj (sp := s₀.gpr .esp) (a := 16) (b := 136 - 16) (by omega),
      (Proof.MlKem.X86.Top.ret_below hsp).sub_right (below_inner (a := 136 - 16) (k := 16) (by omega) hsp)⟩
  · exact ⟨h₀.kSig.sub_left fr, h₀.rSig⟩

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi => by
  simp only [X86.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem nosp_ite {cnd : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite cnd a b) := fun i hi => by
  simp only [X86.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem enter_nosp (si : Nat) (p : Params) : NoSp (enter si p) := fun i hi => by
  simp only [enter, X86.instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rfl

theorem callRet_nosp {rs : List Reg} {n : String} {c : Prog isa} (hc : NoSp c) :
    NoSp (Impl.MlKem.X86.callRet rs n c) := fun i hi => by
  simp only [Impl.MlKem.X86.callRet, X86.instrs, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

/-- `sign_message`, in its leaf. -/
theorem signMessage_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : SignFn p f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 7)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece (SPre p) (SPub p) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ SB p s₀ s) s₀ s') (signMessage n f p) :=
  top_piece (sShape hp) tt (sW p) sign_hW
    (nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_ite (NoSp.of_all (by decide +kernel))
      (nosp_seq (enter_nosp 7 p) (nosp_seq (NoSp.of_all (by decide +kernel))
        (nosp_seq (NoSp.of_all (by decide +kernel)) (callRet_nosp hf.nosp))))))
    (signRest_piece hp hf)

/-- Memory with the arguments `0`, `0x2000`, `0`, `0x2000`, `0`, `0x3000`,
`0x6000` and `0x10000` at `0x5004`. -/
def satMemS : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else
  if a = 0x501d then 0x60 else if a = 0x5022 then 1 else 0

/-- A state satisfying the precondition of `sign_message`. -/
def signSat (p : Params) : State :=
  Proof.MlKem.X86.satState satMemS [⟨0, p.skLen⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, 32⟩]
    [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]

theorem signMessage_verified (hp : p ∈ params) {n : String} {f : Prog isa} (hf : SignFn p f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 7)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Verified X86.target (signMessage n f p) (signMessageContract p X86.abi 136) := by
  refine Piece.verified (((signMessage_piece hp hf tt).pre_mono (fun _ h => sPre_of h)
    fun _ _ _ _ h => spub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hB, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    have h₀' := sPre_of h₀
    sig_post [signMessageContract, signMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [Proof.MlKem.X86.setWidth_append32, hax, hm]
    rcases hB with ⟨h8, h2⟩ | ⟨h8, hout⟩
    · rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; exact h8)]; exact h2
    · rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [signInternal]
      rw [sMu_eq h₀' (skLen_ge hp).1]
      exact hout
  · simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨signSat mlDsa44, by sig_sat_check [signMessageContract, signMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, signSat, Proof.MlKem.X86.satState, satMemS]⟩
    · exact ⟨signSat mlDsa65, by sig_sat_check [signMessageContract, signMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, signSat, Proof.MlKem.X86.satState, satMemS]⟩
    · exact ⟨signSat mlDsa87, by sig_sat_check [signMessageContract, signMessageSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, signSat, Proof.MlKem.X86.satState, satMemS]⟩

end

end VG.Proof.MlDsa.X86.Message

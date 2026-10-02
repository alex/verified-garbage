import VerifiedGarbage.Proof.MlDsa.X86.Message.Shapes
import VerifiedGarbage.Proof.MlKem.X86.TopCall

/-!
# ML-DSA on x86 (32-bit), `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. With `μ` at `X + 840`, the
call of `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)` (`signCall_piece`): its
arguments in `eax`, `ecx`, `edx`, `ebx` and `edi`, pushed; its precondition
(`signContract p X86.abi 96`), from `sign_message`'s; what it leaks, which
is what `sign_message` may (`leak_eq`); and its result, which is
`sign_message`'s.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR LeafEnd)
open VG.Proof.MlKem.X86.Top (entry_regions entry_self covers_of)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- A signing function on `μ`, as `sign_message` calls it. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified X86.target c (signContract p X86.abi 96)
  nosp : NoSp c
  su : stackUse c ≤ 96

/-- The size of the working space of the functions on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × Arg) :=
  [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6), (.edi, .arg 7)]

section
variable (p : Params) (s₀ : State)

/-- The message representative of the run from `s₀`. -/
abbrev sMu : List Byte :=
  H (bytesAt s₀.mem ((arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64) 64 ++ hdrBytes (slay p s₀) ++
    bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++ bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
    64

/-- The regions the signing function on `μ` is given. -/
abbrev sRd : List Region :=
  [⟨(arg s₀ 0).setWidth 64, p.skLen⟩, ⟨((slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩,
    ⟨(arg s₀ 5).setWidth 64, 32⟩]
abbrev sWr : List Region :=
  [⟨(arg s₀ 6).setWidth 64, p.sigLen⟩, ⟨(arg s₀ 7).setWidth 64, sScr p⟩, below (slay p s₀).E1 20]

/-- What `sign_message` changes: `scratch`, the stack, and `sig`. -/
abbrev sW : List Region := [(slay p s₀).SC, (slay p s₀).STK, ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩]

/-- The result. -/
def SB (s : State) : Prop :=
  (arg s₀ 4).toNat < 256 ∧
    Outcome (fun b => signMu p b (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen) (sMu p s₀)
      (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32)) (s.gpr .eax) (bytesAt s.mem ((arg s₀ 6).setWidth 64) p.sigLen)

end

section
variable {p : Params}

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {s₀ : State} (h₀ : SPre p s₀) (h8 : (arg s₀ 4).toNat < 256) (hk : 128 ≤ p.skLen) :
    signMessageLeak p (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
        (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat) (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32) =
      signLeak p (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen) (sMu p s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32) := by
  have := h₀.nSk
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
  simp only [messageRep, skTr, Proof.MlKem.bytesAt_length]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]
  simp only [sMu, hdrBytes, slay, List.append_assoc]
  rw [Proof.MlKem.X86.ea_off (by omega)]


/-- The values of the arguments. -/
theorem signArgs_val {s₀ s s₁ : State} (hc : CtxO (slay p) s₀ s) (hs : SetPost signArgs s s₁) :
    s₁.gpr .eax = arg s₀ 0 ∧ s₁.gpr .ecx = (slay p s₀).X32 + BitVec.ofNat 32 840 ∧ s₁.gpr .edx = arg s₀ 5 ∧
      s₁.gpr .ebx = arg s₀ 6 ∧ s₁.gpr .edi = arg s₀ 7 := by
  have h8 : ∀ {i}, i < 8 → i < (slay p s₀).nA := fun h => h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs.1 (.eax, .arg 0) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.ecx, .off oMU) (by simp), hc.ctx.off]; rfl
  · rw [hs.1 (.edx, .arg 5) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.ebx, .arg 6) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.edi, .arg 7) (by simp), hc.ctx.argV (h8 (by decide))]; rfl

theorem signArgs_ok : argsOk 8 signArgs = true := by decide

/-- The facts about regions the call needs. -/
structure SRegs (p : Params) (s₀ : State) : Prop where
  hE : 120 ≤ (slay p s₀).E1.toNat
  scrSub : Region.Sub ⟨(arg s₀ 7).setWidth 64, sScr p⟩ (slay p s₀).SC
  argsSub : Region.Sub (below (slay p s₀).E1 20) (slay p s₀).STK
  muSub : Region.Sub ⟨((slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (slay p s₀).SC
  kSk : (slay p s₀).STK.Disjoint ⟨(arg s₀ 0).setWidth 64, p.skLen⟩
  kMu : (slay p s₀).STK.Disjoint ⟨((slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩
  kRnd : (slay p s₀).STK.Disjoint ⟨(arg s₀ 5).setWidth 64, 32⟩
  kSig : (slay p s₀).STK.Disjoint ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩
  kScr : (slay p s₀).STK.Disjoint ⟨(arg s₀ 7).setWidth 64, sScr p⟩
  muScr : Region.Disjoint ⟨((slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ ⟨(arg s₀ 7).setWidth 64, sScr p⟩

theorem sregs {s₀ : State} (h₀ : SPre p s₀) (hL : (slay p s₀).Ok) : SRegs p s₀ := by
  have hsp := h₀.sp
  have hE : 120 ≤ (slay p s₀).E1.toNat := by
    show 120 ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]; omega
  have hk : ∀ {R : Region}, (sStk s₀ 136).Disjoint R → (slay p s₀).STK.Disjoint R := fun h =>
    (stk_eq hsp ▸ h).sub_left hL.stk_sub
  have scrSub : Region.Sub ⟨(arg s₀ 7).setWidth 64, sScr p⟩ (slay p s₀).SC :=
    (within_base _ (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega)).sub
  have muSub : Region.Sub ⟨((slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (slay p s₀).SC := by
    rw [mu_eq hL]; exact hL.sub_sc (e := 840) (k := 64) (by omega)
  refine ⟨hE, scrSub, below_sub (by show 20 ≤ 136 - 16; decide) (by show 136 - 16 ≤ _; omega), muSub, hk h₀.kSk, by rw [mu_eq hL]; exact k_mu hL, hk h₀.kRnd,
    hk h₀.kSig, hL.kSC.sub_right scrSub, ?_⟩
  have hx := hL.x_eq
  have := h₀.nScr
  have := mScr_eq p
  have e : ((slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64 =
      (arg s₀ 7).setWidth 64 + BitVec.ofNat 64 (oE p + 840) := by
    rw [mu_eq hL, Lay.MU, hx, add_add]; rfl
  rw [e]
  have d := Offset.disjoint ((arg s₀ 7).setWidth 64) (d := oE p + 840) (n := 64) (e := 0) (k := sScr p)
    (.inr (by simp only [oE, sScr]; omega)) (by omega) (by simp only [oE, sScr] at *; omega)
  rwa [BitVec.add_zero] at d

/-- The callee's precondition. -/
theorem sign_callPre {s₀ s s₁ : State} (h₀ : SPre p s₀) (hc : CtxO (slay p) s₀ s)
    (hs : SetPost signArgs s s₁) : CallPre (signContract p X86.abi 96) Proof.MlKem.X86.rs5 (sRd p s₀) (sWr p s₀) s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx signArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3, v4⟩ := signArgs_val hc hs
  have R := sregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (slay p s₀).E1 := hc1.esp
  have fit : 4 * Proof.MlKem.X86.rs5.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = arg s₀ 0 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v0
  have a1 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 1 = (slay p s₀).X32 + BitVec.ofNat 32 840 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v1
  have a2 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 2 = arg s₀ 5 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v2
  have a3 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 3 = arg s₀ 6 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v3
  have a4 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 4 = arg s₀ 7 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v4
  have eA : argAddr (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = ((slay p s₀).E1 - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hsp1]; rfl
  have eSp : (pushed Proof.MlKem.X86.rs5 s₁).callEntry.gpr .esp = (slay p s₀).E1 - BitVec.ofNat 32 (4 * 5 + 4) := by
    rw [callEntry_esp', hsp1]; rfl
  have cv := covers_of (s := s₁) (n := 5) (rd := sRd p s₀) (wr := sWr p s₀) (fun r hr => ?_) fun r hr => ?_
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact withinRW hc1 ⟨_, List.mem_append_left _ hL.inKey, within_self _⟩
    · exact withinRW hc1 (by rw [mu_eq hL]; exact cov_x hL (e := 840) (k := 64) (by omega))
    · exact withinRW hc1 ⟨_, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (withinW hc1 ⟨_, by show _ ∈ s₀.wr; rw [h₀.wr]; simp, within_self _⟩)
    · exact .inr (withinW hc1 ⟨_, hL.inSC, within_base _ (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega)⟩)
    · exact .inl (by rw [hsp1])
  refine ⟨?_, cv.1, cv.2⟩
  obtain ⟨rSk₁, rSk₂, rSk₃⟩ := entry_regions (E := (slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kSk
  obtain ⟨rMu₁, rMu₂, rMu₃⟩ := entry_regions (E := (slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kMu
  obtain ⟨rRnd₁, rRnd₂, rRnd₃⟩ := entry_regions (E := (slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kRnd
  obtain ⟨rSig₁, rSig₂, rSig₃⟩ := entry_regions (E := (slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kSig
  obtain ⟨rScr₁, rScr₂, rScr₃⟩ := entry_regions (E := (slay p s₀).E1) (k := 5) (K := 96) (by omega) R.kScr
  obtain ⟨rA₂, rA₃⟩ := entry_self (E := (slay p s₀).E1) (k := 5) (K := 96) (by omega)
  generalize he : (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
  sig_pre [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  subst he
  simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp]
  have hX := hL.x32_lt
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (slay p s₀).E1.isLt; omega,
    trivial, trivial, h₀.skSig, h₀.skScr.sub_right R.scrSub, rSk₁, h₀.sigScr.symm.sub_left R.muSub, R.muScr, rMu₁,
    h₀.rndSig, h₀.rndScr.sub_right R.scrSub, rRnd₁, h₀.sigScr.sub_right R.scrSub, rSig₁, rScr₁,
    rSk₂, rMu₂, rRnd₂, rSig₂, rScr₂, rA₂, rSk₃, rMu₃, rRnd₃, rSig₃, rScr₃, rA₃, h₀.nSk,
    by rw [hL.x32_toNat (by omega)]; omega, h₀.nRnd, h₀.nSig,
    by have := h₀.nScr; simp only [mScrLen, messageScratchWords] at this ⊢; omega⟩

/-- What the signing function on `μ` sees on entry. -/
structure SView (p : Params) (s₀ s₁ : State) : Prop where
  a0 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = arg s₀ 0
  a1 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 1 = (slay p s₀).X32 + BitVec.ofNat 32 840
  a2 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 2 = arg s₀ 5
  a3 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 3 = arg s₀ 6
  a4 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 4 = arg s₀ 7
  esp : (pushed Proof.MlKem.X86.rs5 s₁).callEntry.gpr .esp = (slay p s₀).E1 - BitVec.ofNat 32 (4 * 5 + 4)
  bSk : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) p.skLen =
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen
  bMu : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem (((slay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64) 64 =
    sMu p s₀
  bRnd : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem ((arg s₀ 5).setWidth 64) 32 =
    bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32

theorem sign_view {s₀ s s₁ : State} (h₀ : SPre p s₀) (hc : CtxO (slay p) s₀ s)
    (hμ : bytesAt s.mem (slay p s₀).MU 64 = sMu p s₀) (hs : SetPost signArgs s s₁) : SView p s₀ s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx signArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3, v4⟩ := signArgs_val hc hs
  have R := sregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (slay p s₀).E1 := hc1.esp
  have fit : 4 * Proof.MlKem.X86.rs5.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ Proof.MlKem.X86.rs5)
  rw [hsp1] at fr
  have b24 : Region.Sub (below (slay p s₀).E1 (4 * Proof.MlKem.X86.rs5.length + 4)) (slay p s₀).STK :=
    below_sub (by show 24 ≤ 136 - 16; decide) (by show 136 - 16 ≤ _; omega)
  -- Bytes apart from the stack the call uses, as on entry.
  have ent : ∀ {R : Region}, (slay p s₀).STK.Disjoint R → R.len ≤ 2 ^ 64 →
      bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem R.base R.len = bytesAt s₁.mem R.base R.len :=
    fun {R} hR hn => Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hR.sub_left b24).symm) hn hi
  have hsp := h₀.sp
  have p0 : ∀ {R : Region}, (sStk s₀ 136).Disjoint R → (slay p s₀).SC.Disjoint R → R.len ≤ 2 ^ 64 →
      bytesAt s₁.mem R.base R.len = bytesAt s₀.mem R.base R.len := fun {R} hk hx hn => by
    have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by show 16 ≤ _; omega)
    rw [hs.2.mem, hc.ctx.bytesAt_eq hx ((stk_eq hsp ▸ hk).sub_left hL.stk_sub) hn]
    exact Proof.MlKem.bytesAt_congr fun _ hi => hf.bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((stk_eq hsp ▸ hk).sub_left (below_sub (by decide) hsp)).symm) hn hi
  refine ⟨by rw [callEntry_arg fit (by decide) (by decide)]; exact v0,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v1,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v2,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v3,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v4,
    by rw [callEntry_esp', hsp1]; rfl, ?_, ?_, ?_⟩
  · rw [ent (R := ⟨_, p.skLen⟩) R.kSk (by show p.skLen ≤ 2 ^ 64; have := h₀.nSk; omega)]
    exact p0 (R := ⟨_, p.skLen⟩) h₀.kSk h₀.skScr.symm (by show p.skLen ≤ 2 ^ 64; have := h₀.nSk; omega)
  · rw [ent (R := ⟨_, 64⟩) R.kMu (by show 64 ≤ 2 ^ 64; decide), hs.2.mem, mu_eq hL]; exact hμ
  · rw [ent (R := ⟨_, 32⟩) R.kRnd (by show 32 ≤ 2 ^ 64; decide)]
    exact p0 (R := ⟨_, 32⟩) h₀.kRnd h₀.rndScr.symm (by show 32 ≤ 2 ^ 64; decide)

/-- The call of the signing function on `μ`. -/
theorem signCall_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : SignFn p f) :
    Piece (SPre p) (SPub p) (fun s₀ s => CtxO (slay p) s₀ s ∧ bytesAt s.mem (slay p s₀).MU 64 = sMu p s₀)
      (fun s₀ s => LeafEnd s₀ (sW p s₀) s ∧ SB p s₀ s)
      (.seq (.block (setArgs signArgs)) (Impl.MlKem.X86.callRet rs5 n f)) := by
  refine argsRet_piece hf.ver.1 hf.ver.2.1 hf.nosp (by decide) (by decide) (by taint_decide) (sShape hp).pubL
    (fun _ _ _ h => h.1) (fun _ _ => by show argsOk 8 signArgs = true; decide) (sRd p) (sWr p)
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · refine ⟨?_, ?_⟩
    · simp only [sRd, Lay.X32, slay, hq.args 0 (by decide), hq.args 5 (by decide), hq.args 7 (by decide)]
    · simp only [sWr, Lay.E1, slay, hq.esp, hq.args 6 (by decide), hq.args 7 (by decide)]
  · have := hf.su
    have := h₀.sp
    show _ ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]
    simp only [List.length_cons, List.length_nil]
    omega
  · exact sign_callPre h₀ ha.1 hs
  · obtain ⟨hc, hμ⟩ := ha
    obtain ⟨hc', hμ'⟩ := ha'
    have hp' := (sShape hp).pubL s₀ s₀' h₀ h₀' hq
    have hk := (skLen_ge hp).1
    have lk := (leak_eq h₀ hc.ok.ctxLt hk).symm.trans (hq.leak.trans (leak_eq h₀' hc'.ok.ctxLt hk))
    obtain ⟨a0, a1, a2, a3, a4, eS, bSk, bMu, bRnd⟩ := sign_view h₀ hc hμ hs
    obtain ⟨a0', a1', a2', a3', a4', eS', bSk', bMu', bRnd'⟩ := sign_view h₀' hc' hμ' hs'
    generalize (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 a4 eS bSk bMu bRnd ⊢
    generalize (pushed Proof.MlKem.X86.rs5 s₁').callEntry = e' at a0' a1' a2' a3' a4' eS' bSk' bMu' bRnd' ⊢
    sig_pub [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eS, eS']
    rw [bSk, bMu, bRnd, bSk', bMu', bRnd']
    exact ⟨by simp only [Lay.E1, hp'.sp], lk, hq.args 0 (by decide), by rw [hp'.x], hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)⟩
  · obtain ⟨hc, hμ⟩ := ha
    have hL := hc.ok
    have R := sregs h₀ hL
    have hE := R.hE
    have hsp1 : s₁.gpr .esp = (slay p s₀).E1 := (SetPost.ctx signArgs_ok hs hc.ctx).esp
    refine ⟨CtxO.leafEnd (sShape hp) h₀ hc (W := sW p s₀) (by simp) (rs := sWr p s₀ ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs5.length + stackUse f + 4)]) (by rw [← hs.2.mem]; exact fr)
        (fun r hr => ?_) ((e₃ .esp (by decide)).trans (hs.esp signArgs_ok)) (e₁.trans hs.2.rd)
        (e₂.trans hs.2.wr), ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(arg s₀ 6).setWidth 64, p.sigLen⟩, by simp, fun _ h => h⟩
      · exact ⟨(slay p s₀).SC, by simp, R.scrSub⟩
      · exact ⟨(slay p s₀).STK, by simp, R.argsSub⟩
      · refine ⟨(slay p s₀).STK, by simp, ?_⟩
        rw [hsp1]
        have := hf.su
        exact below_sub (by show _ ≤ 136 - 16; simp only [List.length_cons, List.length_nil]; omega)
          (by show 136 - 16 ≤ _; omega)
    · have v := sign_view h₀ hc hμ hs
      obtain ⟨s₂, m₂, g₂, post⟩ := post
      obtain ⟨a0, a1, a2, a3, -, -, bSk, bMu, bRnd⟩ := v
      generalize (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 bSk bMu bRnd post
      sig_post [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
      simp only [arg_withRegions, a0, a1, a2, a3] at post
      rw [bSk, bMu, bRnd, Proof.MlKem.X86.setWidth_append32, g₂, m₂] at post
      exact ⟨hc.ok.ctxLt, post⟩

end

end VG.Proof.MlDsa.X86.Message

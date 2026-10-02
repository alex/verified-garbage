import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign

/-!
# ML-DSA on x86 (32-bit), `verify_message`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. With `μ` at `X + 840`, the
call of `vg_mldsa*_verify(pk, μ, sig, scratch)` (`verifyCall_piece`): its
arguments in `eax`, `ecx`, `edx` and `ebx`, pushed; its precondition
(`verifyContract p X86.abi 96`), from `verify_message`'s; what it leaks, its
inputs, which `verify_message`'s inputs determine; and its result, which is
`verify_message`'s.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR LeafEnd)
open VG.Proof.MlKem.X86.Top (entry_regions entry_self covers_of)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- A verification function on `μ`, as `verify_message` calls it. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified X86.target c (verifyContract p X86.abi 96)
  nosp : NoSp c
  su : stackUse c ≤ 96

/-- The arguments of the call of the verification function on `μ`, and their registers. -/
abbrev verifyArgs : List (Reg × Arg) := [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6)]
abbrev rs4 : List Reg := [.ebx, .edx, .ecx, .eax]

section
variable (p : Params) (s₀ : State)

/-- The message representative of the run from `s₀`. -/
abbrev vMu : List Byte :=
  H (H (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) 64 ++ hdrBytes (vlay p s₀) ++
    bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++ bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
    64

/-- The regions the verification function on `μ` is given. -/
abbrev vRd : List Region :=
  [⟨(arg s₀ 0).setWidth 64, p.pkLen⟩, ⟨((vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩,
    ⟨(arg s₀ 5).setWidth 64, p.sigLen⟩]
abbrev vWr : List Region := [⟨(arg s₀ 6).setWidth 64, sScr p⟩, below (vlay p s₀).E1 16]

/-- What `verify_message` changes: `scratch` and the stack. -/
abbrev vW : List Region := [(vlay p s₀).SC, (vlay p s₀).STK]

/-- The result. -/
def VB (s : State) : Prop :=
  (arg s₀ 4).toNat < 256 ∧
    ((s.gpr .eax = 1 ∧ ∃ b, verifyMu p b (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) (vMu p s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen) = some true) ∨
      (s.gpr .eax = 0 ∧ verifyMu p minBounds (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) (vMu p s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen) ≠ some true))

end

section
variable {p : Params}

theorem verifyArgs_ok : argsOk 7 verifyArgs = true := by decide

/-- The values of the arguments. -/
theorem verifyArgs_val {s₀ s s₁ : State} (hc : CtxO (vlay p) s₀ s) (hs : SetPost verifyArgs s s₁) :
    s₁.gpr .eax = arg s₀ 0 ∧ s₁.gpr .ecx = (vlay p s₀).X32 + BitVec.ofNat 32 840 ∧ s₁.gpr .edx = arg s₀ 5 ∧
      s₁.gpr .ebx = arg s₀ 6 := by
  have h7 : ∀ {i}, i < 7 → i < (vlay p s₀).nA := fun h => h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs.1 (.eax, .arg 0) (by simp), hc.ctx.argV (h7 (by decide))]; rfl
  · rw [hs.1 (.ecx, .off oMU) (by simp), hc.ctx.off]; rfl
  · rw [hs.1 (.edx, .arg 5) (by simp), hc.ctx.argV (h7 (by decide))]; rfl
  · rw [hs.1 (.ebx, .arg 6) (by simp), hc.ctx.argV (h7 (by decide))]; rfl

/-- The facts about regions the call needs. -/
structure VRegs (p : Params) (s₀ : State) : Prop where
  hE : 116 ≤ (vlay p s₀).E1.toNat
  scrSub : Region.Sub ⟨(arg s₀ 6).setWidth 64, sScr p⟩ (vlay p s₀).SC
  argsSub : Region.Sub (below (vlay p s₀).E1 16) (vlay p s₀).STK
  muSub : Region.Sub ⟨((vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (vlay p s₀).SC
  kPk : (vlay p s₀).STK.Disjoint ⟨(arg s₀ 0).setWidth 64, p.pkLen⟩
  kMu : (vlay p s₀).STK.Disjoint ⟨((vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩
  kSig : (vlay p s₀).STK.Disjoint ⟨(arg s₀ 5).setWidth 64, p.sigLen⟩
  kScr : (vlay p s₀).STK.Disjoint ⟨(arg s₀ 6).setWidth 64, sScr p⟩
  muScr : Region.Disjoint ⟨((vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ ⟨(arg s₀ 6).setWidth 64, sScr p⟩

theorem vregs {s₀ : State} (h₀ : VPre p s₀) (hL : (vlay p s₀).Ok) : VRegs p s₀ := by
  have hsp := h₀.sp
  have hE : 116 ≤ (vlay p s₀).E1.toNat := by
    show 116 ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]; omega
  have hk : ∀ {R : Region}, (sStk s₀ 132).Disjoint R → (vlay p s₀).STK.Disjoint R := fun h =>
    (stk_eq hsp ▸ h).sub_left hL.stk_sub
  have scrSub : Region.Sub ⟨(arg s₀ 6).setWidth 64, sScr p⟩ (vlay p s₀).SC :=
    (within_base _ (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega)).sub
  have muSub : Region.Sub ⟨((vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (vlay p s₀).SC := by
    rw [mu_eq hL]; exact hL.sub_sc (e := 840) (k := 64) (by omega)
  refine ⟨hE, scrSub, below_sub (by show 16 ≤ 132 - 16; decide) (by show 132 - 16 ≤ _; omega), muSub, hk h₀.kPk,
    by rw [mu_eq hL]; exact k_mu hL, hk h₀.kSig, hL.kSC.sub_right scrSub, ?_⟩
  have hx := hL.x_eq
  have := h₀.nScr
  have := mScr_eq p
  have e : ((vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64 =
      (arg s₀ 6).setWidth 64 + BitVec.ofNat 64 (oE p + 840) := by
    rw [mu_eq hL, Lay.MU, hx, add_add]; rfl
  rw [e]
  have d := Offset.disjoint ((arg s₀ 6).setWidth 64) (d := oE p + 840) (n := 64) (e := 0) (k := sScr p)
    (.inr (by simp only [oE, sScr]; omega)) (by omega) (by simp only [oE, sScr] at *; omega)
  rwa [BitVec.add_zero] at d

/-- The callee's precondition. -/
theorem verify_callPre {s₀ s s₁ : State} (h₀ : VPre p s₀) (hc : CtxO (vlay p) s₀ s)
    (hs : SetPost verifyArgs s s₁) : CallPre (verifyContract p X86.abi 96) rs4 (vRd p s₀) (vWr p s₀) s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx verifyArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3⟩ := verifyArgs_val hc hs
  have R := vregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (vlay p s₀).E1 := hc1.esp
  have fit : 4 * rs4.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed rs4 s₁).callEntry 0 = arg s₀ 0 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v0
  have a1 : arg (pushed rs4 s₁).callEntry 1 = (vlay p s₀).X32 + BitVec.ofNat 32 840 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v1
  have a2 : arg (pushed rs4 s₁).callEntry 2 = arg s₀ 5 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v2
  have a3 : arg (pushed rs4 s₁).callEntry 3 = arg s₀ 6 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v3
  have eA : argAddr (pushed rs4 s₁).callEntry 0 = ((vlay p s₀).E1 - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0, hsp1]; rfl
  have eSp : (pushed rs4 s₁).callEntry.gpr .esp = (vlay p s₀).E1 - BitVec.ofNat 32 (4 * 4 + 4) := by
    rw [callEntry_esp', hsp1]; rfl
  have cv := covers_of (s := s₁) (n := 4) (rd := vRd p s₀) (wr := vWr p s₀) (fun r hr => ?_) fun r hr => ?_
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact withinRW hc1 ⟨_, List.mem_append_left _ hL.inKey, within_self _⟩
    · exact withinRW hc1 (by rw [mu_eq hL]; exact cov_x hL (e := 840) (k := 64) (by omega))
    · exact withinRW hc1 ⟨_, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (withinW hc1 ⟨_, hL.inSC, within_base _
        (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega)⟩)
    · exact .inl (by rw [hsp1])
  refine ⟨?_, cv.1, cv.2⟩
  obtain ⟨rPk₁, rPk₂, rPk₃⟩ := entry_regions (E := (vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kPk
  obtain ⟨rMu₁, rMu₂, rMu₃⟩ := entry_regions (E := (vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kMu
  obtain ⟨rSig₁, rSig₂, rSig₃⟩ := entry_regions (E := (vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kSig
  obtain ⟨rScr₁, rScr₂, rScr₃⟩ := entry_regions (E := (vlay p s₀).E1) (k := 4) (K := 96) (by omega) R.kScr
  obtain ⟨rA₂, rA₃⟩ := entry_self (E := (vlay p s₀).E1) (k := 4) (K := 96) (by omega)
  generalize he : (pushed rs4 s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
  sig_pre [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  subst he
  simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
  have hX := hL.x32_lt
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (vlay p s₀).E1.isLt; omega,
    trivial, trivial, h₀.pkScr.sub_right R.scrSub, rPk₁, R.muScr, rMu₁, h₀.sigScr.sub_right R.scrSub, rSig₁, rScr₁,
    rPk₂, rMu₂, rSig₂, rScr₂, rA₂, rPk₃, rMu₃, rSig₃, rScr₃, rA₃, h₀.nPk,
    by rw [hL.x32_toNat (by omega)]; omega, h₀.nSig,
    by have := h₀.nScr; simp only [mScrLen, messageScratchWords] at this ⊢; omega⟩


/-- What the verification function on `μ` sees on entry. -/
structure VView (p : Params) (s₀ s₁ : State) : Prop where
  a0 : arg (pushed rs4 s₁).callEntry 0 = arg s₀ 0
  a1 : arg (pushed rs4 s₁).callEntry 1 = (vlay p s₀).X32 + BitVec.ofNat 32 840
  a2 : arg (pushed rs4 s₁).callEntry 2 = arg s₀ 5
  a3 : arg (pushed rs4 s₁).callEntry 3 = arg s₀ 6
  esp : (pushed rs4 s₁).callEntry.gpr .esp = (vlay p s₀).E1 - BitVec.ofNat 32 (4 * 4 + 4)
  bPk : bytesAt (pushed rs4 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) p.pkLen =
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen
  bMu : bytesAt (pushed rs4 s₁).callEntry.mem (((vlay p s₀).X32 + BitVec.ofNat 32 840).setWidth 64) 64 = vMu p s₀
  bSig : bytesAt (pushed rs4 s₁).callEntry.mem ((arg s₀ 5).setWidth 64) p.sigLen =
    bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen

theorem verify_view {s₀ s s₁ : State} (h₀ : VPre p s₀) (hc : CtxO (vlay p) s₀ s)
    (hμ : bytesAt s.mem (vlay p s₀).MU 64 = vMu p s₀) (hs : SetPost verifyArgs s s₁) : VView p s₀ s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx verifyArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3⟩ := verifyArgs_val hc hs
  have R := vregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (vlay p s₀).E1 := hc1.esp
  have fit : 4 * rs4.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ rs4)
  rw [hsp1] at fr
  have b20 : Region.Sub (below (vlay p s₀).E1 (4 * rs4.length + 4)) (vlay p s₀).STK :=
    below_sub (by show 20 ≤ 132 - 16; decide) (by show 132 - 16 ≤ _; omega)
  have ent : ∀ {a : Addr} {n : Nat}, (vlay p s₀).STK.Disjoint ⟨a, n⟩ → n ≤ 2 ^ 64 →
      bytesAt (pushed rs4 s₁).callEntry.mem a n = bytesAt s₁.mem a n :=
    fun {a n} hR hn => Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := ⟨a, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hR.sub_left b20).symm) hn hi
  have hsp := h₀.sp
  have p0 : ∀ {a : Addr} {n : Nat}, (sStk s₀ 132).Disjoint ⟨a, n⟩ → (vlay p s₀).SC.Disjoint ⟨a, n⟩ → n ≤ 2 ^ 64 →
      bytesAt s₁.mem a n = bytesAt s₀.mem a n := fun {a n} hk hx hn => by
    rw [hs.2.mem, hc.ctx.bytesAt_eq hx ((stk_eq hsp ▸ hk).sub_left hL.stk_sub) hn]
    exact p0_bytes (by decide) hsp hk hn
  refine ⟨by rw [callEntry_arg fit (by decide) (by decide)]; exact v0,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v1,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v2,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v3,
    by rw [callEntry_esp', hsp1]; rfl, ?_, ?_, ?_⟩
  · rw [ent R.kPk (by have := h₀.nPk; omega)]
    exact p0 h₀.kPk h₀.pkScr.symm (by have := h₀.nPk; omega)
  · rw [ent R.kMu (by decide), hs.2.mem, mu_eq hL]; exact hμ
  · rw [ent R.kSig (by have := h₀.nSig; omega)]
    exact p0 h₀.kSig h₀.sigScr.symm (by have := h₀.nSig; omega)

/-- Two runs with the same public data have the same `μ`, and the same inputs. -/
theorem vInputs_pub {s₀ s₀' : State} (hq : VPub p s₀ s₀') :
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen = bytesAt s₀'.mem ((arg s₀' 0).setWidth 64) p.pkLen ∧
      vMu p s₀ = vMu p s₀' ∧
      bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen = bytesAt s₀'.mem ((arg s₀' 5).setWidth 64) p.sigLen := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := leak4 (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length, hq.args 2 (by decide)])
    (by simp only [Proof.MlKem.bytesAt_length, hq.args 4 (by decide)]) hq.leak
  refine ⟨e₁, ?_, e₄⟩
  simp only [vMu, hdrBytes, vlay, e₁, e₂, e₃]
  rw [hq.args 4 (by decide)]

/-- The call of the verification function on `μ`. -/
theorem verifyCall_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : VerifyFn p f) :
    Piece (VPre p) (VPub p) (fun s₀ s => CtxO (vlay p) s₀ s ∧ bytesAt s.mem (vlay p s₀).MU 64 = vMu p s₀)
      (fun s₀ s => LeafEnd s₀ (vW p s₀) s ∧ VB p s₀ s)
      (.seq (.block (setArgs verifyArgs)) (Impl.MlKem.X86.callRet rs4 n f)) := by
  refine argsRet_piece hf.ver.1 hf.ver.2.1 hf.nosp (by decide) (by decide) (by taint_decide) (vShape hp).pubL
    (fun _ _ _ h => h.1) (fun _ _ => verifyArgs_ok) (vRd p) (vWr p)
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => verify_callPre h₀ ha.1 hs)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · refine ⟨?_, ?_⟩
    · simp only [vRd, Lay.X32, vlay, hq.args 0 (by decide), hq.args 5 (by decide), hq.args 6 (by decide)]
    · simp only [vWr, Lay.E1, vlay, hq.esp, hq.args 6 (by decide)]
  · have := hf.su
    have := h₀.sp
    show _ ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega)]
    simp only [List.length_cons, List.length_nil]
    omega
  · obtain ⟨hc, hμ⟩ := ha
    obtain ⟨hc', hμ'⟩ := ha'
    have hp' := (vShape hp).pubL s₀ s₀' h₀ h₀' hq
    obtain ⟨i₁, i₂, i₃⟩ := vInputs_pub hq
    obtain ⟨a0, a1, a2, a3, eS, bPk, bMu, bSig⟩ := verify_view h₀ hc hμ hs
    obtain ⟨a0', a1', a2', a3', eS', bPk', bMu', bSig'⟩ := verify_view h₀' hc' hμ' hs'
    generalize (pushed rs4 s₁).callEntry = e at a0 a1 a2 a3 eS bPk bMu bSig ⊢
    generalize (pushed rs4 s₁').callEntry = e' at a0' a1' a2' a3' eS' bPk' bMu' bSig' ⊢
    sig_pub [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eS, eS']
    rw [bPk, bMu, bSig, bPk', bMu', bSig', i₁, i₂, i₃]
    exact ⟨by simp only [Lay.E1, hp'.sp], rfl, hq.args 0 (by decide), by rw [hp'.x], hq.args 5 (by decide),
      hq.args 6 (by decide)⟩
  · obtain ⟨hc, hμ⟩ := ha
    have hL := hc.ok
    have R := vregs h₀ hL
    have hE := R.hE
    have hsp1 : s₁.gpr .esp = (vlay p s₀).E1 := (SetPost.ctx verifyArgs_ok hs hc.ctx).esp
    refine ⟨CtxO.leafEnd (vShape hp) h₀ hc (W := vW p s₀) (by simp) (rs := vWr p s₀ ++
        [below (s₁.gpr .esp) (4 * rs4.length + stackUse f + 4)]) (by rw [← hs.2.mem]; exact fr)
        (fun r hr => ?_) ((e₃ .esp (by decide)).trans (hs.esp verifyArgs_ok)) (e₁.trans hs.2.rd)
        (e₂.trans hs.2.wr), ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨(vlay p s₀).SC, by simp, R.scrSub⟩
      · exact ⟨(vlay p s₀).STK, by simp, R.argsSub⟩
      · refine ⟨(vlay p s₀).STK, by simp, ?_⟩
        rw [hsp1]
        have := hf.su
        exact below_sub (by show _ ≤ 132 - 16; simp only [List.length_cons, List.length_nil]; omega)
          (by show 132 - 16 ≤ _; omega)
    · have v := verify_view h₀ hc hμ hs
      obtain ⟨s₂, -, g₂, post⟩ := post
      obtain ⟨a0, a1, a2, -, -, bPk, bMu, bSig⟩ := v
      generalize (pushed rs4 s₁).callEntry = e at a0 a1 a2 bPk bMu bSig post
      sig_post [verifyContract, verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
      simp only [arg_withRegions, a0, a1, a2] at post
      rw [bPk, bMu, bSig, Proof.MlKem.X86.setWidth_append32, g₂] at post
      exact ⟨hc.ok.ctxLt, post⟩

end

end VG.Proof.MlDsa.X86.Message

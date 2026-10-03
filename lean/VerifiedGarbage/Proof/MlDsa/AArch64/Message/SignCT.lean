import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT

/-!
# ML-DSA on AArch64, `sign_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which includes what
`signMessageLeak` says (`signI`), leak the same: the branch on `ctx_len`,
the entry and the exit depend only on the pointers and the lengths; the
hashing leaks only the layout (`muHash_tr`); and the call of the signing
function on `μ` leaks only `signLeak` of the key, `μ` and `rnd`, which is
`signMessageLeak` of the inputs (`signCall_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def signI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop :=
  signMessageLeak p (bytesAt m₁ L.key p.skLen) (bytesAt m₁ L.msg L.len.toNat) (bytesAt m₁ L.ctx L.ctxLen.toNat)
      (bytesAt m₁ L.rnd 32) =
    signMessageLeak p (bytesAt m₂ L.key p.skLen) (bytesAt m₂ L.msg L.len.toNat)
      (bytesAt m₂ L.ctx L.ctxLen.toNat) (bytesAt m₂ L.rnd 32)

/-- The layout is that of a run of `sign_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def SOk (p : Params) (L : Lay) (m : Mem) : Prop :=
  ∃ σ, SPre p σ ∧ (σ.gpr .x4).toNat < 256 ∧ slay p σ = L ∧ σ.mem = m

/-- `μ` at `X + 840`. -/
def MuOk (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {L : Lay} (hL : L.Ok) (hk : L.keyLen = p.skLen) (m : Mem) :
    signMessageLeak p (bytesAt m L.key p.skLen) (bytesAt m L.msg L.len.toNat) (bytesAt m L.ctx L.ctxLen.toNat)
        (bytesAt m L.rnd 32) =
      signLeak p (bytesAt m L.key p.skLen) (H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ hdrBytes L ++
        bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64) (bytesAt m L.rnd 32) := by
  have := hL.hKey
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hL.ctxLt)]
  simp only [messageRep, skTr, hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]

/-- What a layout of `sign_message` says of `rnd`, `sig` and `scratch`. -/
structure SFacts (p : Params) (L : Lay) : Prop where
  key : L.keyLen = p.skLen
  xRnd : L.XS.Disjoint ⟨L.rnd, 32⟩
  kRnd : L.STK.Disjoint ⟨L.rnd, 32⟩
  inRnd : (⟨L.rnd, 32⟩ : Region) ∈ L.rd
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.wr
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, sScr p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

theorem SOk.facts {L : Lay} {m : Mem} (h : SOk p L m) : SFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.rndScr.symm.sub_left (slay_X p σ).sub, hσ.stkRnd, by simp [slay, hσ.rd],
    by simp [slay, hσ.wr], ⟨⟨σ.gpr .x7, mScrLen p⟩, by simp [slay, hσ.wr],
      within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩,
    ⟨⟨σ.gpr .x7, mScrLen p⟩, by simp [slay, hσ.wr], mu_within p σ⟩⟩

/-- Two runs of the call of the signing function on `μ`. -/
theorem signCall_tr {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m t => SOk p L m ∧ MuOk L m t) (callA n c signArgs) fun _ _ => True := by
  refine call_tr (by decide) hS.ver.1 hS.ver.2.1
    (fun L => [⟨L.key, p.skLen⟩, ⟨L.MU, 64⟩, ⟨L.rnd, 32⟩]) (fun L => [⟨L.sig, p.sigLen⟩, ⟨L.scr, sScr p⟩])
    (fun L g v m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g v m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ, hσ, h8, rfl, -⟩, -⟩ := hφ
    exact signK_pre hp hσ h8 hc hm.1 (hm.2.sp.trans hc.sp)
  · obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁.1
    have F := φ₁.1.facts
    obtain ⟨x0, x1, x2, x3, x4⟩ := signRegs_of c₁ f₁.1
    obtain ⟨y0, y1, y2, y3, y4⟩ := signRegs_of c₂ f₂.1
    have hk := hL.hKey
    have ek : ∀ {g v m₀} {a a1 : State}, Ctx (slay p σ) g v m₀ a → Moved signArgs a a1 →
        bytesAt a1.mem (σ.gpr .x0) p.skLen = bytesAt m₀ (σ.gpr .x0) p.skLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (slay p σ).key) hL.xKey hL.kKey (by have := hL.nKey; simp only [slay] at this ⊢; omega)
    have er : ∀ {g v m₀} {a a1 : State}, Ctx (slay p σ) g v m₀ a → Moved signArgs a a1 →
        bytesAt a1.mem (σ.gpr .x5) 32 = bytesAt m₀ (σ.gpr .x5) 32 := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (slay p σ).rnd) F.xRnd F.kRnd (by decide)
    have eμ : ∀ {a a1 : State}, Moved signArgs a a1 →
        bytesAt a1.mem (slay p σ).MU 64 = bytesAt a.mem (slay p σ).MU 64 := fun f => by rw [f.2.mem]
    sig_pub [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
    simp only [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, and_true]
    refine ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], ?_⟩
    rw [ek c₁ f₁, ek c₂ f₂, er c₁ f₁, er c₂ f₂, eμ f₁, eμ f₂, φ₁.2, φ₂.2]
    have := hi
    unfold signI at this
    rw [leak_eq hL F.key, leak_eq hL F.key] at this
    exact this
  · have F := hφ.1.facts
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (F.key ▸ hL.inKey), within_self _⟩
      · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
      · exact ⟨_, List.mem_append_left _ F.inRnd, within_self _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, F.inSig, within_self _⟩
      · exact F.inScr

/-- The public data of the contract, spelled out. -/
structure SPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : signMessageLeak p (bytesAt s₁.mem (s₁.gpr .x0) p.skLen) (bytesAt s₁.mem (s₁.gpr .x1) (s₁.gpr .x2).toNat)
      (bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat) (bytesAt s₁.mem (s₁.gpr .x5) 32) =
    signMessageLeak p (bytesAt s₂.mem (s₂.gpr .x0) p.skLen) (bytesAt s₂.mem (s₂.gpr .x1) (s₂.gpr .x2).toNat)
      (bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat) (bytesAt s₂.mem (s₂.gpr .x5) 32)
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  x4 : s₁.gpr .x4 = s₂.gpr .x4
  x5 : s₁.gpr .x5 = s₂.gpr .x5
  x6 : s₁.gpr .x6 = s₂.gpr .x6
  x7 : s₁.gpr .x7 = s₂.gpr .x7

theorem sPub_of {s₁ s₂ : State} (h : (signMessageContract p AArch64.abi 16).pub s₁ s₂) : SPub p s₁ s₂ := by
  sig_pub [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : SPre p s₁) (h₂ : SPre p s₂) (h : SPub p s₁ s₂) : slay p s₁ = slay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [rKey, rMsg, rCtx, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [h.x6, h.x7]
  simp only [slay, h.sp, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, e1, e2]

/-- The body, between the entry and the exit: its runs end with the same
`x28` and stack pointer. -/
theorem signBody_tr (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : SignFn p c)
    (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m _ => SOk p L m)
      (.seq (muHash v.callee (.slotOff fKey 64)) (callA n c signArgs))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  have side : ∀ L : Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ R) ∧
      Region.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ := fun L hL => by
    have := hL.hKey
    have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
    have hst : Region.Sub ⟨L.ST, 200⟩ L.XS := by
      have := Offset.sub_base L.X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [x0] using this
    exact ⟨⟨_, List.mem_append_left _ hL.inKey, w⟩, (hL.xKey.symm.sub_left w.sub).sub_right hst,
      (hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right w.sub⟩
  have mh := muHash_tr v (I := signI p) (Φ := fun L m _ => SOk p L m) (tr := .slotOff fKey 64) (by decide) rfl
    (fun L => L.key + BitVec.ofNat 64 64) (fun L g vv m t hc => hc.slotOffV 64) side
  have mh' := two_wp (I := signI p) (Φ := fun L m _ => SOk p L m) (Ψ := fun L m t => SOk p L m ∧ MuOk L m t) mh
    fun L g vv m₀ t hL hc hφ => by
      have := hL.hKey
      have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
      obtain ⟨a, b, c, d⟩ := side L hL
      refine WP.mono (muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl (fun t' hc' => hc'.slotOffV 64)
        a b c d) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ, ?_⟩
      unfold MuOk
      rw [hμ, hc.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)]
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    (mh'.seq (signCall_tr hS hp)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : Lay} {g vv m₀} {t : State}, L.Ok → Ctx L g vv m₀ t → SOk p L m₀ →
        WP isa (.seq (muHash v.callee (.slotOff fKey 64)) (callA n c signArgs)) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc hφ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d⟩ := side _ hL
      refine WP.seq (WP.mono (muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl
        (fun t' hc' => hc'.slotOffV 64) a b c d) fun t₁ ⟨hc₁, _⟩ => ?_)
      exact WP.mono (signCall_ok hS hp hσ h8 hc₁) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (p : Params) (x y : State) : Prop :=
  (signMessageContract p AArch64.abi 16).pre x ∧ (signMessageContract p AArch64.abi 16).pre y ∧
    (signMessageContract p AArch64.abi 16).pub x y

/-- After the shift of `ctx_len`. -/
abbrev ALsr (x s1 : State) : Prop :=
  Only [.x9] x s1 ∧ isa.eval (.nonzero .x .x9) s1 = some (decide ¬ (x.gpr .x4).toNat < 256)

theorem lsr_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.lsr .x .x9 .x4 8]) (.block [])).isSome = true := by rfl

theorem movz2_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.movz .x .x0 2 0]) (.block [])).isSome = true := by rfl

theorem leave_taint : (taint.check (AArch64.Taint.ofRegs [.x28]) (.block leave) (.block [])).isSome = true := by
  rfl

theorem enterS_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs [.x7]) (.block (enter .x7 p signSaves)) (.block [])).isSome = true := by
  rfl

theorem signMessage_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : SignFn p c)
    (hp : p ∈ params) :
    ConstantTime isa (signMessageContract p AArch64.abi 16).pre (signMessageContract p AArch64.abi 16).pub
      (signMessage v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (signMessageContract p AArch64.abi 16).pre s₁ ∧
      (signMessageContract p AArch64.abi 16).pre s₂ ∧ (signMessageContract p AArch64.abi 16).pub s₁ s₂) =
      Ghost (SP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `x9 ← ctx_len >> 8`.
  have hlsr := ghost_step (P := SP2 p) (A := fun x a => a = x) (B := ALsr) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(sPub_of hxy.2.2).sp, by simp⟩) lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨lsr_ok _, lsr_ok _⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, (sPub_of hxy.2.2).x4]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.sp, f₂.1.sp]; exact (sPub_of hxy.2.2).sp, by simp⟩) movz2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => ALsr x a ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (slay p x) a.gpr a.v a.mem t
    have hent := ghost_step (P := SP2 p) (A := A) (B := B) (c := .block (enter .x7 p signSaves))
      (AArch64.taintRel [.x7] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (sPub_of hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.get .x7, f₂.1.1.get .x7]; exact (sPub_of hxy.2.2).x7⟩) (enterS_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (signMessageContract p AArch64.abi 16).pre x' → A x' a' →
            WP isa (.block (enter .x7 p signSaves)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := slay_ok hp (sPre_of hx) h8
          exact WP.mono (enter_ok hL rfl (by decide) rfl (o.get .x7) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (signSaves_vals o) (by decide)) fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← (sPub_of hxy.2.2).x4, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq (RelCT.mono (signBody_tr v hS hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩,
      ⟨h8y, b', mb, cb⟩⟩ => ?_) fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) leave_taint))
    have hx := sPre_of hxy.1
    have hy := sPre_of hxy.2.1
    have hpub := sPub_of hxy.2.2
    have e := slay_eq hx hy hpub
    refine ⟨slay p x, a'.gpr, b'.gpr, a'.v, b'.v, a'.mem, b'.mem, slay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold signI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.AArch64.Message

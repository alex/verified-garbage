import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT

/-!
# ML-DSA on ARMv7, `verify_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which include `pk`, the
message, the context string and the signature (`verifyI`), leak the same:
the branch on `ctx_len`, the entry and the exit depend only on the pointers
and the lengths; the hashing leaks only the layout (`trHash_tr`,
`muHash_tr`); and the call of the verification function on `μ` leaks only
`pk`, `μ` and `sig`, which are the same in both runs (`verifyCall_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : Lay) (m : Mem) : List Byte :=
  bytesAt m (State.addr L.key) p.pkLen ++ bytesAt m (State.addr L.msg) L.len.toNat ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.sig) p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop := leakBytes (vIn p L m₁) = leakBytes (vIn p L m₂)

theorem verifyI_eq {L : Lay} {m₁ m₂ : Mem} (h : verifyI p L m₁ m₂) :
    bytesAt m₁ (State.addr L.key) p.pkLen = bytesAt m₂ (State.addr L.key) p.pkLen ∧
      bytesAt m₁ (State.addr L.msg) L.len.toNat = bytesAt m₂ (State.addr L.msg) L.len.toNat ∧
      bytesAt m₁ (State.addr L.ctx) L.ctxLen.toNat = bytesAt m₂ (State.addr L.ctx) L.ctxLen.toNat ∧
      bytesAt m₁ (State.addr L.sig) p.sigLen = bytesAt m₂ (State.addr L.sig) p.sigLen :=
  leak4 (by simp only [Proof.MlKem.bytesAt_length]) (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length]) h

/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : Lay) (m : Mem) : Prop :=
  ∃ σ, VPre p σ ∧ (stackArg σ 0).toNat < 256 ∧ vlay p σ = L ∧ σ.mem = m

/-- `tr` at `X + 840`. -/
def TrOk (p : Params) (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m (State.addr L.key) p.pkLen) 64

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m (State.addr L.key) p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.msg) L.len.toNat) 64

/-- What a layout of `verify_message` says of `sig` and `scratch`. -/
structure VFacts (p : Params) (L : Lay) : Prop where
  key : L.keyLen = p.pkLen
  xSig : L.SC.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  kSig : L.STK.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 32
  inSig : (⟨State.addr L.sig, p.sigLen⟩ : Region) ∈ L.rd

theorem VOk.facts {L : Lay} {m : Mem} (h : VOk p L m) : VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.sigScr.symm, hσ.stkSig, hσ.nSig, by simp [vlay, hσ.rd]⟩

/-- The regions the verification function on `μ` is given, as functions of the layout. -/
abbrev vRd (p : Params) (L : Lay) : List Region :=
  [⟨State.addr L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨State.addr L.sig, p.sigLen⟩]
abbrev vWr (p : Params) (L : Lay) : List Region := [⟨State.addr L.scr, sScr p⟩]

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ VMuOk p L m t)
      (.seq (.block (setArgs verifyArgs)) (.call n c)) fun _ _ => True := by
  refine RelCT.seq (setArgs_two (by decide)) ?_
  refine RelCT.mono (P := fun a1 b1 => ∃ L : Lay, ∃ x y, (∃ g₁ g₂ m₁ m₂, L.Ok ∧ verifyI p L m₁ m₂ ∧
      Ctx L g₁ m₁ x ∧ Ctx L g₂ m₂ y ∧ (VOk p L m₁ ∧ VMuOk p L m₁ x) ∧ (VOk p L m₂ ∧ VMuOk p L m₂ y)) ∧
      Moved verifyArgs x a1 ∧ Moved verifyArgs y b1)
    (RelCT.exists_ fun L => RelCT.call hV.ver.1 hV.ver.2.1 (vRd p L) (vWr p L) fun a1 b1 h => ?_)
    (fun a1 b1 ⟨x, y, ⟨L, hp'⟩, f₁, f₂⟩ => ⟨L, x, y, hp', f₁, f₂⟩) fun _ _ h => h
  obtain ⟨x, y, ⟨g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, ⟨φ₁, μ₁⟩, ⟨_, μ₂⟩⟩, f₁, f₂⟩ := h
  have F := φ₁.facts
  obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁
  have hL' := vlay_ok hp hσ h8
  have pre₁ := verifyK_pre hp hσ h8 c₁ f₁.1 (f₁.2.sp.trans c₁.sp)
  have pre₂ := verifyK_pre hp hσ h8 c₂ f₂.1 (f₂.2.sp.trans c₂.sp)
  have cv : ∀ {t t1 : State} {g m₀}, Ctx (vlay p σ) g m₀ t → Moved verifyArgs t t1 →
      Covers (vRd p (vlay p σ) ++ vWr p (vlay p σ)) (t1.rd ++ t1.wr) ∧ Covers (vWr p (vlay p σ)) t1.wr :=
    fun hc f => by
      rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
      have hw : ∀ r ∈ vWr p (vlay p σ), ∃ R ∈ (vlay p σ).wr, Within r R := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, hL'.inSC, within_base _ (by simp only [vlay]; rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
      refine ⟨covers_of_within fun r hr => ?_, covers_of_within hw⟩
      rcases List.mem_append.mp hr with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact ⟨_, List.mem_append_left _ (F.key ▸ hL'.inKey), within_self _⟩
        · exact ⟨_, List.mem_append_right _ hL'.inSC, mu_within hL'⟩
        · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
      · obtain ⟨R, hR, w⟩ := hw r h
        exact ⟨R, List.mem_append_right _ hR, w⟩
  refine ⟨pre₁, pre₂, ?_, (cv c₁ f₁).1, (cv c₁ f₁).2, (cv c₂ f₂).1, (cv c₂ f₂).2⟩
  obtain ⟨x0, x1, x2, x3⟩ := verifyRegs_of hL' c₁ f₁.1
  obtain ⟨y0, y1, y2, y3⟩ := verifyRegs_of hL' c₂ f₂.1
  have ek : ∀ {g m₀} {a a1 : State}, Ctx (vlay p σ) g m₀ a → Moved verifyArgs a a1 →
      bytesAt a1.mem (State.addr (σ.gpr .r0)) p.pkLen = bytesAt m₀ (State.addr (σ.gpr .r0)) p.pkLen := fun c f => by
    rw [f.2.mem]
    exact c.bytesAt_eq (p := State.addr (vlay p σ).key) hL'.xKey hL'.kKey (by have := hσ.nPk; omega)
  have es : ∀ {g m₀} {a a1 : State}, Ctx (vlay p σ) g m₀ a → Moved verifyArgs a a1 →
      bytesAt a1.mem (State.addr (stackArg σ 1)) p.sigLen = bytesAt m₀ (State.addr (stackArg σ 1)) p.sigLen :=
    fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := State.addr (vlay p σ).sig) F.xSig F.kSig (by have := F.nSig; omega)
  have eμ : ∀ {a a1 : State}, Moved verifyArgs a a1 →
      bytesAt a1.mem (State.addr ((vlay p σ).X32 + BitVec.ofNat 32 840)) 64 = bytesAt a.mem (vlay p σ).MU 64 :=
    fun f => by rw [f.2.mem, mu_eq hL']
  obtain ⟨ik, im, ic, is⟩ := verifyI_eq hi
  have sw : ∀ a : BitVec 32, BitVec.setWidth 64 a = State.addr a := fun _ => rfl
  sig_pub [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [x0, x1, x2, x3, y0, y1, y2, y3, sw, and_true]
  refine ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], ?_⟩
  rw [ek c₁ f₁, ek c₂ f₂, es c₁ f₁, es c₂ f₂, eμ f₁, eμ f₂, μ₁, μ₂]
  have ik' : bytesAt m₁ (State.addr (σ.gpr .r0)) p.pkLen = bytesAt m₂ (State.addr (σ.gpr .r0)) p.pkLen := ik
  have is' : bytesAt m₁ (State.addr (stackArg σ 1)) p.sigLen = bytesAt m₂ (State.addr (stackArg σ 1)) p.sigLen := is
  rw [ik, im, ic, ik', is']

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.pkLen ++
      bytesAt s₁.mem (State.addr (s₁.gpr .r1)) (s₁.gpr .r2).toNat ++
      bytesAt s₁.mem (State.addr (s₁.gpr .r3)) (stackArg s₁ 0).toNat ++
      bytesAt s₁.mem (State.addr (stackArg s₁ 1)) p.sigLen) =
    leakBytes (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.pkLen ++
      bytesAt s₂.mem (State.addr (s₂.gpr .r1)) (s₂.gpr .r2).toNat ++
      bytesAt s₂.mem (State.addr (s₂.gpr .r3)) (stackArg s₂ 0).toNat ++
      bytesAt s₂.mem (State.addr (stackArg s₂ 1)) p.sigLen)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1
  a2 : stackArg s₁ 2 = stackArg s₂ 2

theorem vPub_of {s₁ s₂ : State} (h : (verifyMessageContract p Arm.abi 36).pub s₁ s₂) : VPub p s₁ s₂ := by
  sig_pub [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VPre p s₁) (h₂ : VPre p s₂) (h : VPub p s₁ s₂) : vlay p s₁ = vlay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]
    simp only [rKey, rMsg, rCtx, rArgs, sArg, stackArgAddr0, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [sArg, h.a2]
  simp only [vlay, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2, e1, e2]

/-- The body, between the entry and the exit: its runs end with the same
`r7` and stack pointer. -/
theorem verifyBody_tr {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m _ => VOk p L m)
      (.seq (trHash p) (.seq (muHash (.off oMU)) (.seq (.block (setArgs verifyArgs)) (.call n c))))
      fun a b => a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp := by
  have th := trHash_tr (I := verifyI p) (Φ := fun L m _ => VOk p L m) (pkLen_ge hp).2
    (fun _ _ _ h => h.facts.key)
  have th' := two_wp (I := verifyI p) (Φ := fun L m _ => VOk p L m) (Ψ := fun L m t => VOk p L m ∧ TrOk p L m t) th
    fun L g m₀ t hL hc hφ => WP.mono (trHash_ok hL hφ.facts.key hc) fun t' ⟨hc', htr⟩ =>
      ⟨hc', hφ, by unfold TrOk; rw [htr, hφ.facts.key]⟩
  have side : ∀ L : Lay, L.Ok → (L.X32 + BitVec.ofNat 32 840).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 840), 64⟩ := fun L hL => by
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    rw [mu_eq hL]
    exact ⟨by have := hL.x32_lt; rw [x32_toNat hL (by omega)]; omega, ⟨R, by simp [hR], hw⟩, st_mu.symm, mu_ks,
      k_mu hL⟩
  have mh := muHash_tr (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t) (tr := .off oMU)
    (by decide) rfl (fun L => L.X32 + BitVec.ofNat 32 840) (fun L g m t _ hc => hc.off oMU) side
  have mh' := two_wp (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t)
    (Ψ := fun L m t => VOk p L m ∧ VMuOk p L m t) mh fun L g m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e⟩ := side L hL
      refine WP.mono (muHash_ok hL hc (tr := .off oMU) (trp := L.X32 + BitVec.ofNat 32 840) (by decide) rfl
        (fun t' hc' => hc'.off oMU) a b c d e) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ.1, ?_⟩
      unfold VMuOk
      rw [hμ]
      have h2 := hφ.2
      unfold TrOk at h2
      rw [mu_eq hL, h2]
  refine RelCT.postDep (F := fun x x' => x'.gpr .r7 = x.gpr .r7 ∧ x'.sp = x.sp)
    (th'.seq (mh'.seq (verifyCall_tr hV hp))) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : Lay} {g m₀} {t : State}, L.Ok → Ctx L g m₀ t → VOk p L m₀ →
        WP isa (.seq (trHash p) (.seq (muHash (.off oMU)) (.seq (.block (setArgs verifyArgs)) (.call n c)))) t
          fun t' => t'.gpr .r7 = t.gpr .r7 ∧ t'.sp = t.sp := fun hL hc hφ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d, e⟩ := side _ hL
      refine WP.seq (WP.mono (trHash_ok hL rfl hc) fun t₁ ⟨hc₁, _⟩ => ?_)
      refine WP.seq (WP.mono (muHash_ok hL hc₁ (tr := .off oMU) (trp := (vlay p σ).X32 + BitVec.ofNat 32 840)
        (by decide) rfl (fun t' hc' => hc'.off oMU) a b c d e) fun t₂ ⟨hc₂, _⟩ => ?_)
      exact WP.mono (verifyCall_ok hV hp hσ h8 hc₂) fun s' ⟨hf, _⟩ =>
        ⟨hf.r7.trans hc.r7.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.r7, c₂.r7], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- Two states with the stack pointer, permissions and memory of two entry
states agreeing on the public data agree on the first `n ≤ 12` bytes of the
arguments on the stack. -/
theorem vAgree {x y a b : State} (hx : VPre p x) (hy : VPre p y) (hpub : VPub p x y)
    (ha : a.sp = x.sp ∧ a.wr = x.wr ∧ a.mem = x.mem) (hb : b.sp = y.sp ∧ b.wr = y.wr ∧ b.mem = y.mem)
    {n : Nat} (hn : n ≤ 12) : VG.Arm.Taint.Agree (argTaint [] n) a b := by
  have w : ∀ {z c : State}, VPre p z → c.sp = z.sp ∧ c.wr = z.wr ∧ c.mem = z.mem →
      c.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ c.wr, Region.Disjoint ⟨State.addr c.sp, n⟩ r := fun {z c} hz hc => by
    refine ⟨by rw [hc.1]; have := hz.spA; omega, fun r hr => ?_⟩
    rw [hc.2.1, hz.wr] at hr
    have hs : Region.Sub ⟨State.addr c.sp, n⟩ (rArgs z 12) := by
      simp only [rArgs, stackArgAddr0, hc.1]; exact Region.sub_prefix hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (hz.scrArgs.sub_right hs).symm
  have hsp : a.sp = b.sp := by rw [ha.1, hb.1, hpub.sp]
  refine agree_argTaint (fun r hr => by simp at hr) hsp (w hx ha) (w hy hb) fun k hk => ?_
  exact argMem_of (s₁ := a) (s₂ := b) (j := 3) hsp (by rw [ha.1]; have := hx.spA; omega) (fun i hi => by
    simp only [stackArg, stackArgAddr, ha.1, hb.1, ha.2.2, hb.2.2]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hpub.a0
    · exact hpub.a1
    · exact hpub.a2) k (by omega)

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageContract p Arm.abi 36).pre x ∧ (verifyMessageContract p Arm.abi 36).pre y ∧
    (verifyMessageContract p Arm.abi 36).pub x y

theorem enterV_taint (p : Params) :
    (VG.Arm.taint.check (argTaint [] 12) (.block (enter 8 p verifyLoads)) (.block [])).isSome = true := by
  rfl

theorem verifyMessage_ct {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    ConstantTime isa (verifyMessageContract p Arm.abi 36).pre (verifyMessageContract p Arm.abi 36).pub
      (verifyMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageContract p Arm.abi 36).pre s₁ ∧
      (verifyMessageContract p Arm.abi 36).pre s₂ ∧ (verifyMessageContract p Arm.abi 36).pub s₁ s₂) =
      Ghost (VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessage top
  have hchk := ghost_step (P := VP2 p) (A := fun x a => a = x) (B := AChk)
    (c := .block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)])
    (argRel [] 4 (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂
      exact vAgree (vPre_of hxy.1) (vPre_of hxy.2.1) (vPub_of hxy.2.2) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by omega))
      chk_taint)
    fun x y a b hxy e₁ e₂ => by
      subst e₁ e₂; exact ⟨chk_ok ((vPre_of hxy.1).args (by omega)), chk_ok ((vPre_of hxy.2.1).args (by omega))⟩
  refine RelCT.seq hchk (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, (vPub_of hxy.2.2).a0]) ?_ ?_)
  · exact taintRel [] (fun _ _ _ r hr => by simp at hr) mov2_taint
  · let A : State → State → Prop := fun x a => AChk x a ∧ isa.eval .ne a = some false
    let B : State → State → Prop := fun x t => (stackArg x 0).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (vlay p x) a.gpr a.mem t
    have hent := ghost_step (P := VP2 p) (A := A) (B := B) (c := .block (enter 8 p verifyLoads))
      (argRel [] 12 (fun a b ⟨x, y, hxy, f₁, f₂⟩ =>
        vAgree (vPre_of hxy.1) (vPre_of hxy.2.1) (vPub_of hxy.2.2) ⟨f₁.1.1.sp, f₁.1.1.wr, f₁.1.1.mem⟩
          ⟨f₂.1.1.sp, f₂.1.1.wr, f₂.1.1.mem⟩ (Nat.le_refl _)) (enterV_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (verifyMessageContract p Arm.abi 36).pre x' → A x' a' →
            WP isa (.block (enter 8 p verifyLoads)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (stackArg x' 0).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have h := vPre_of hx
          have hL := vlay_ok hp h h8
          have hs1 : ∀ o', o' + 4 ≤ 12 → a'.mem.readW (State.addr (a'.sp + BitVec.ofNat 32 o')) 32 =
              x'.mem.readW (State.addr (x'.sp + BitVec.ofNat 32 o')) 32 := fun _ _ => by rw [o.mem, o.sp]
          exact WP.mono (enter_ok hL rfl (nA := 12) (by decide) (by omega) o.sp
            (by rw [o.rd]; rfl) (by rw [o.wr]; rfl) (o.get .r0) (o.get .r1) (o.get .r2) (o.get .r3)
            (fun o' ho => by rw [o.rd, o.wr, o.sp]; exact h.args ho) (by rw [o.sp]; exact h.spA)
            (by rw [o.sp, ← stackArgAddr0]; exact h.scrArgs) (by omega)
            (by rw [hs1 8 (by omega)]; exact stackArg_eq x' 2) (by decide) (fun j hj => by
              have hj4 : j < 4 := hj
              rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
              · exact (hs1 0 (by decide)).trans (stackArg_eq x' 0)
              · exact (hs1 4 (by decide)).trans (stackArg_eq x' 1)
              · exact (hs1 4 (by decide)).trans (stackArg_eq x' 1)
              · exact (hs1 8 (by decide)).trans (stackArg_eq x' 2)))
            fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← (vPub_of hxy.2.2).a0, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h)
      (RelCT.seq (RelCT.mono (verifyBody_tr hV hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩,
        ⟨h8y, b', mb, cb⟩⟩ => ?_) fun _ _ h => h) (taintRel [.r7] (fun a b h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1) leave_taint))
    have hx := vPre_of hxy.1
    have hy := vPre_of hxy.2.1
    have hpub := vPub_of hxy.2.2
    have e := vlay_eq hx hy hpub
    refine ⟨vlay p x, a'.gpr, b'.gpr, a'.mem, b'.mem, vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.r0, ← hpub.r1, ← hpub.r2, ← hpub.r3, ← hpub.a0, ← hpub.a1] at lk
    unfold verifyI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.Arm.Message

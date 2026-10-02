import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCorrect
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT

/-!
# ML-DSA on x86-64, `verify_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which include `pk`, the
message, the context string and the signature (`verifyI`), leak the same:
the branch on `ctx_len`, the moves and the frame depend only on the pointers
and the lengths; the hashing leaks only the layout (`trHash_tr`,
`muHash_tr`); and the call of the verification function on `μ` leaks only
`pk`, `μ` and `sig`, which are the same in both runs (`verifyCall_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)
open VG.Proof.MlDsa.X86_64.Verify (verifyK)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : Lay) (m : Mem) : List Byte :=
  bytesAt m L.key p.pkLen ++ bytesAt m L.msg L.len.toNat ++ bytesAt m L.ctx L.ctxLen.toNat ++
    bytesAt m L.sig p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop := leakBytes (vIn p L m₁) = leakBytes (vIn p L m₂)

theorem verifyI_eq {L : Lay} {m₁ m₂ : Mem} (h : verifyI p L m₁ m₂) :
    bytesAt m₁ L.key p.pkLen = bytesAt m₂ L.key p.pkLen ∧
      bytesAt m₁ L.msg L.len.toNat = bytesAt m₂ L.msg L.len.toNat ∧
      bytesAt m₁ L.ctx L.ctxLen.toNat = bytesAt m₂ L.ctx L.ctxLen.toNat ∧
      bytesAt m₁ L.sig p.sigLen = bytesAt m₂ L.sig p.sigLen := by
  have e := leakBytes_inj h
  obtain ⟨e, e₄⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  obtain ⟨e, e₃⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  obtain ⟨e₁, e₂⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  exact ⟨e₁, e₂, e₃, e₄⟩

/-- `tr` at `X + 840`. -/
def TrOk (p : Params) (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m L.key p.pkLen) 64

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m L.key p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ VMuOk p L m t) (callA n c (verifyArgs p))
      fun _ _ => True := by
  refine call_tr (verifyArgs_ok hp) hV.ok hV.ct (verifyRd p) (verifyWr p)
    (fun L g mx m₀ t t1 hL hc hφ hm => verifyK_pre hp hL hφ.1.facts hc hm)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g mx m₀ t hL hc hφ => ?_)
  · have F := φ₁.1.facts
    obtain ⟨x1, x2, x3, x4⟩ := verifyRegsL F.e c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := verifyRegsL F.e c₂ f₂
    have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
    simp only [verifyK, Verify.vPk, Verify.vMu, Verify.vSig, State.withRegions_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_rsp, x1, x2, x3, x4, y1, y2, y3, y4, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs),
      f₂.2.gpr (by decide : Reg.rsp ∉ argRegs), c₁.rsp, c₂.rsp, true_and]
    have hk := hL.nKey
    rw [F.key] at hk
    have ce : ∀ {g mx m₀} {a a1 : State} {q : Addr} {k : Nat}, Ctx L g mx m₀ a → Moved (verifyArgs p) a a1 →
        Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 8⟩ ⟨q, k⟩ → k ≤ 2 ^ 64 →
        bytesAt a1.callEntry.mem q k = bytesAt a.mem q k := fun c f hd hn => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (argRegs_cs r hr)).ce_bytesAt hd hn, f.1.2.1]
    have dk := hL.stk_r (hkey ▸ hL.kKey) (d := 24) (n := 8) (by decide)
    have dμ := hL.stk_x (d := 24) (n := 8) (e := 840) (k := 64) (by decide) (by decide)
    have ds := hL.stk_r F.kSig (d := 24) (n := 8) (by decide)
    have hsx : L.XS.Disjoint ⟨L.sig, p.sigLen⟩ := by
      have hX : Within L.XS ⟨L.scr, mScrLen p⟩ := ⟨L.E, rfl, by rw [mScr_eq, F.e]⟩
      exact F.sigScr.symm.sub_left hX.sub
    have ns := F.nSig
    obtain ⟨ek, -, ec, es⟩ := verifyI_eq hi
    obtain ⟨-, em, -, -⟩ := verifyI_eq hi
    refine ⟨?_, ?_, ?_⟩
    · rw [ce c₁ f₁ dk (by omega), ce c₂ f₂ dk (by omega), c₁.bytesAt_eq (hkey ▸ hL.xKey) (hkey ▸ hL.kKey) (by omega),
        c₂.bytesAt_eq (hkey ▸ hL.xKey) (hkey ▸ hL.kKey) (by omega), ek]
    · rw [ce c₁ f₁ dμ (by decide), ce c₂ f₂ dμ (by decide), φ₁.2, φ₂.2, ek, ec, em]
    · rw [ce c₁ f₁ ds (by omega), ce c₂ f₂ ds (by omega), c₁.bytesAt_eq hsx F.kSig (by omega),
        c₂.bytesAt_eq hsx F.kSig (by omega), es]
  · have F := hφ.1.facts
    have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ hL.inKey, by rw [hkey]; exact within_self _⟩
      · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
      · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact F.inScr

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  leak : leakBytes (bytesAt s₁.mem (s₁.gpr .rdi) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx).toNat ++
      bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat ++ bytesAt s₁.mem (s₁.gpr .r9) p.sigLen) =
    leakBytes (bytesAt s₂.mem (s₂.gpr .rdi) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx).toNat ++
      bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat ++ bytesAt s₂.mem (s₂.gpr .r9) p.sigLen)
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0

theorem vPub_of {s₁ s₂ : State} (h : (verifyMessageContract p X86_64.abi 104).pub s₁ s₂) : VPub p s₁ s₂ := by
  sig_pub [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VPre p s₁) (h₂ : VPre p s₂) (h : VPub p s₁ s₂) : vlay p s₁ = vlay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [vPk, rMsg, rCtx, vSigR, vArgs, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8,
      h.r9, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [vScr, h.a0]
  simp only [vlay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, e1, e2]

/-- The body of the frame. -/
theorem verifyBody_tr {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m _ => VOk p L m)
      (.seq (trHash p) (.seq (muHash p (aMu p)) (callA n c (verifyArgs p)))) fun _ _ => True := by
  have hE := oE_lt hp
  have hk := (pkLen_ge hp).2
  have th := trHash_tr (I := verifyI p) (Φ := fun L m _ => VOk p L m) hE hk
    (fun _ _ _ h => ⟨h.facts.e, h.facts.key⟩)
  have th' := two_wp (I := verifyI p) (Φ := fun L m _ => VOk p L m) (Ψ := fun L m t => VOk p L m ∧ TrOk p L m t) th
    fun L g mx m₀ t hL hc hφ => WP.mono (trHash_ok hL hφ.facts.e hφ.facts.key hc) fun t' ⟨hc', _, htr⟩ =>
      ⟨hc', hφ, by unfold TrOk; rw [htr, hφ.facts.key]⟩
  have hok : (aMu p).ok = true := by simp [Arg.ok, Impl.MlDsa.X86_64.Message.aMu, fScr]; omega
  have mh := muHash_tr (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t) hE
    (fun _ _ _ h => h.1.facts.e) (tr := aMu p) hok (fun L => L.MU)
    (fun L g mx m t hc hE => hc.aMu p hE)
    fun L hL => by
      obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
      exact ⟨⟨R, by simp [hR], hw⟩, st_mu.symm, mu_ks, k_mu hL⟩
  have mh' := two_wp (I := verifyI p) (Φ := fun L m t => VOk p L m ∧ TrOk p L m t)
    (Ψ := fun L m t => VOk p L m ∧ VMuOk p L m t) mh fun L g mx m₀ t hL hc hφ => by
      obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
      refine WP.mono (muHash_ok hL hφ.1.facts.e hc (tr := aMu p) hok (fun t' hc' => hc'.aMu p hφ.1.facts.e)
        ⟨R, by simp [hR], hw⟩ st_mu.symm mu_ks (k_mu hL)) fun t' ⟨hc', _, hμ⟩ => ⟨hc', hφ.1, ?_⟩
      unfold VMuOk
      rw [hμ, hφ.2]
  exact th'.seq (mh'.seq (verifyCall_tr hV hp))

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageContract p X86_64.abi 104).pre x ∧ (verifyMessageContract p X86_64.abi 104).pre y ∧
    (verifyMessageContract p X86_64.abi 104).pub x y

/-- After the moves before the push. -/
abbrev VMov (x x2 : State) : Prop :=
  (x.gpr .r8).toNat < 256 ∧ ((x2.gpr .r11 = stackArg x 0 ∧ x2.gpr .rax = 0 ∧
    x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧ (∀ r, r ∉ [Reg.r11, .rax] → x2.gpr r = x.gpr r) ∧
    x2.rd = x.rd ∧ x2.wr = x.wr)

theorem verifyMessage_ct {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    ConstantTime isa (verifyMessageContract p X86_64.abi 104).pre (verifyMessageContract p X86_64.abi 104).pub
      (verifyMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageContract p X86_64.abi 104).pre s₁ ∧
      (verifyMessageContract p X86_64.abi 104).pre s₂ ∧ (verifyMessageContract p X86_64.abi 104).pub s₁ s₂) =
      Ghost (VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessage top
  -- `cmp r8, 256`.
  have hcmp := ghost_step (P := VP2 p) (A := fun x a => a = x) (B := ACmp) (c := .block [.alu .cmp .r8 (.imm 256)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (vPub_of hxy.2.2).rsp)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨cmp_ok _, cmp_ok _⟩
  refine RelCT.seq hcmp (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.2.2.2.2, f₂.2.2.2.2.2, (vPub_of hxy.2.2).r8]) ?_ ?_)
  · -- `ctx_len < 256`.
    have hmov := ghost_step (P := VP2 p) (A := fun x a => ACmp x a ∧ (x.gpr .r8).toNat < 256) (B := VMov)
      (c := .block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)])
      (block_rsp_tr (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact spOnly_nomem (fun _ => rfl) rfl)
        fun a b ⟨x, y, hxy, f₁, f₂⟩ => by rw [f₁.1.1, f₂.1.1]; exact (vPub_of hxy.2.2).rsp)
      fun x y a b hxy f₁ f₂ => by
        have mv : ∀ {x a : State}, (verifyMessageContract p X86_64.abi 104).pre x → ACmp x a →
            (x.gpr .r8).toNat < 256 → WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) a
              (VMov x) := fun hx f h8 =>
          WP.mono (verifyMov_ok (vPre_of hx) f.1 f.2.1 f.2.2.1) fun x2 ⟨h, k⟩ =>
            ⟨h8, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans f.2.2.2.2.1⟩,
              fun r hr => (k.gpr hr).trans (by rw [f.1]), k.2.1.trans f.2.2.1, k.2.2.trans f.2.2.2.1⟩
        exact ⟨mv hxy.1 f₁.1 f₁.2, mv hxy.2.1 f₂.1 f₂.2⟩
    refine RelCT.seq (RelCT.mono hmov (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, ?_⟩, ⟨f₂, ?_⟩⟩)
      fun _ _ h => h) ?_
    · rw [f₁.2.2.2.2.2] at hc; simpa using hc
    · rw [f₁.2.2.2.2.2, (vPub_of hxy.2.2).r8, ← f₂.2.2.2.2.2] at hc
      rw [f₂.2.2.2.2.2] at hc; simpa using hc
    refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
      rw [f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide)]; exact (vPub_of hxy.2.2).rsp) ?_
    -- The frame's body, from the push.
    let A : State → State → Prop := fun x a => ∃ s₁, VMov x s₁ ∧ a = pushed verifyRegs s₁
    let B : State → State → Prop := fun x t => (x.gpr .r8).toNat < 256 ∧ Ctx (vlay p x) x.gpr x.mxcsr x.mem t
    have hdr := ghost_step (P := VP2 p) (A := A) (B := B) (c := .block setHdr)
      (block_rsp_tr (fun i hi => by
          simp only [setHdr, List.mem_singleton] at hi; subst hi
          exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩)
        fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
          subst e₁ e₂
          rw [pushed_rsp, pushed_rsp, f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide), (vPub_of hxy.2.2).rsp])
      fun x y a b hxy fa fb => by
        have en : ∀ {x a : State}, (verifyMessageContract p X86_64.abi 104).pre x → A x a →
            WP isa (.block setHdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
          subst e
          have h := vPre_of hx
          have hL := vlay_ok hp h f.1
          refine WP.mono (entry_ok hL rfl (by decide) (by rw [f.2.2.1 _ (by decide), vlay_B])
            (f.2.2.2.1.trans rfl) (f.2.2.2.2.trans rfl) (verifyRegs_vals f.2.2.1 f.2.1.1 f.2.1.2.1)
            (f.2.2.1 _ (by decide))) fun t ⟨hc, _, _⟩ =>
            ⟨f.1, hc.congr (fun r hr _ => f.2.2.1 r (cs_tmpV r hr)) f.2.1.2.2.2 f.2.1.2.2.1⟩
        exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hdr (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
      ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ⟨h8x, ca⟩, ⟨h8y, cb⟩⟩ => ?_)
      (verifyBody_tr hV hp)
    have hx := vPre_of hxy.1
    have hy := vPre_of hxy.2.1
    have hpub := vPub_of hxy.2.2
    have e := vlay_eq hx hy hpub
    refine ⟨vlay p x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, rfl⟩, ⟨y, hy, h8y, e.symm, rfl⟩⟩
    have lk := hpub.leak
    rw [← hpub.rdi, ← hpub.rsi, ← hpub.rdx, ← hpub.rcx, ← hpub.r8, ← hpub.r9] at lk
    exact lk
  · exact block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ => by rw [f₁.1, f₂.1]; exact (vPub_of hxy.2.2).rsp

end

end VG.Proof.MlDsa.X86_64.Message

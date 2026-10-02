import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT

/-!
# ML-DSA on x86-64, `sign_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which includes what
`signMessageLeak` says (`signI`), leak the same: the branch on `ctx_len`,
the moves and the frame depend only on the pointers and the lengths; the
hashing leaks only the layout (`muHash_tr`); and the call of the signing
function on `μ` leaks only `signLeak` of the key, `μ` and `rnd`, which is
`signMessageLeak` of the inputs (`signCall_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)
open VG.Proof.MlDsa.X86_64.Sign (signK scrLen)
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
  ∃ σ, SPre p σ ∧ (σ.gpr .r8).toNat < 256 ∧ slay p σ = L ∧ σ.mem = m

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
  e : oE p = L.E
  xRnd : L.XS.Disjoint ⟨L.rnd, 32⟩
  kRnd : L.STK.Disjoint ⟨L.rnd, 32⟩
  inRnd : (⟨L.rnd, 32⟩ : Region) ∈ L.rd
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.wr
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, scrLen p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

theorem SOk.facts {L : Lay} {m : Mem} (h : SOk p L m) : SFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, rfl, hσ.rndScr.symm.sub_left (slay_X p σ).sub, hσ.stkRnd, by simp [slay, hσ.rd],
    by simp [slay, hσ.wr], ⟨rScr p σ, by simp [slay, hσ.wr], within_base _ (by rw [mScr_eq]; simp [scrLen, oE])⟩,
    ⟨rScr p σ, by simp [slay, hσ.wr], mu_within p σ⟩⟩

/-- The registers after the moves of the arguments of the signing function on `μ`. -/
theorem signRegsL {L : Lay} (hE : oE p = L.E) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g mx m₀ t) (hm : Moved (signArgs p) t t1) :
    t1.gpr .rdi = L.key ∧ t1.gpr .rsi = L.MU ∧ t1.gpr .rdx = L.rnd ∧ t1.gpr .rcx = L.sig ∧
      t1.gpr .r8 = L.scr := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hm.1.1
  rw [hc.slot, fKey, hc.pKey] at e1
  rw [hc.aMu p hE] at e2
  rw [hc.slot, fRnd, hc.pRnd] at e3
  rw [hc.slot, fSig, hc.pSig] at e4
  rw [hc.slot, fScr, hc.pScr] at e5
  exact ⟨e1, e2, e3, e4, e5⟩

/-- Two runs of the call of the signing function on `μ`. -/
theorem signCall_tr {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m t => SOk p L m ∧ MuOk L m t) (callA n c (signArgs p)) fun _ _ => True := by
  refine call_tr (signArgs_ok hp) hS.ok hS.ct
    (fun L => [⟨L.key, p.skLen⟩, ⟨L.MU, 64⟩, ⟨L.rnd, 32⟩]) (fun L => [⟨L.sig, p.sigLen⟩, ⟨L.scr, scrLen p⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g mx m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ, hσ, h8, rfl, -⟩, -⟩ := hφ
    exact signK_pre hp hσ h8 hc hm
  · have F := φ₁.1.facts
    obtain ⟨x1, x2, x3, x4, x5⟩ := signRegsL F.e c₁ f₁
    obtain ⟨y1, y2, y3, y4, y5⟩ := signRegsL F.e c₂ f₂
    have hc₁ := c₁.regs f₁.2.2.1 f₁.2.2.2 f₁.1.2.1 f₁.1.2.2 fun r hr => f₁.2.gpr (argRegs_cs r hr)
    have hc₂ := c₂.regs f₂.2.2.1 f₂.2.2.2 f₂.1.2.1 f₂.1.2.2 fun r hr => f₂.2.gpr (argRegs_cs r hr)
    simp only [signK, State.withRegions_mem, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce,
      x1, x2, x3, y1, y2, y3, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, true_and]
    refine ⟨x4.trans y4.symm, x5.trans y5.symm, ?_⟩
    have hk := hL.hKey
    have hkk := F.key
    have ek : ∀ {g mx m₀} {a a1 : State}, Ctx L g mx m₀ a → Moved (signArgs p) a a1 →
        bytesAt a1.callEntry.mem L.key p.skLen = bytesAt m₀ L.key p.skLen := fun c f => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (argRegs_cs r hr)).ce_bytesAt
        (hL.stk_r (r := ⟨L.key, p.skLen⟩) (F.key ▸ hL.kKey) (d := 24) (n := 8) (by decide)) (by omega),
        f.1.2.1, c.bytesAt_eq (F.key ▸ hL.xKey) (F.key ▸ hL.kKey) (by omega)]
    have er : ∀ {g mx m₀} {a a1 : State}, Ctx L g mx m₀ a → Moved (signArgs p) a a1 →
        bytesAt a1.callEntry.mem L.rnd 32 = bytesAt m₀ L.rnd 32 := fun c f => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (argRegs_cs r hr)).ce_bytesAt
        (hL.stk_r F.kRnd (d := 24) (n := 8) (by decide)) (by decide), f.1.2.1,
        c.bytesAt_eq F.xRnd F.kRnd (by decide)]
    have eμ : ∀ {g mx m₀} {a a1 : State}, Ctx L g mx m₀ a → Moved (signArgs p) a a1 →
        bytesAt a1.callEntry.mem L.MU 64 = bytesAt a.mem L.MU 64 := fun c f => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (argRegs_cs r hr)).ce_bytesAt
        (hL.stk_x (d := 24) (n := 8) (e := 840) (k := 64) (by decide) (by decide)) (by decide), f.1.2.1]
    rw [ek c₁ f₁, ek c₂ f₂, er c₁ f₁, er c₂ f₂, eμ c₁ f₁, eμ c₂ f₂, φ₁.2, φ₂.2,
      Sign.signLeakT_eq_signLeak, Sign.signLeakT_eq_signLeak, ← leak_eq hL F.key, ← leak_eq hL F.key]
    exact hi
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
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  leak : signMessageLeak p (bytesAt s₁.mem (s₁.gpr .rdi) p.skLen) (bytesAt s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx).toNat)
      (bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat) (bytesAt s₁.mem (s₁.gpr .r9) 32) =
    signMessageLeak p (bytesAt s₂.mem (s₂.gpr .rdi) p.skLen) (bytesAt s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx).toNat)
      (bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat) (bytesAt s₂.mem (s₂.gpr .r9) 32)
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1

theorem sPub_of {s₁ s₂ : State} (h : (signMessageContract p X86_64.abi 104).pub s₁ s₂) : SPub p s₁ s₂ := by
  sig_pub [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : SPre p s₁) (h₂ : SPre p s₂) (h : SPub p s₁ s₂) : slay p s₁ = slay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [rSk, rMsg, rCtx, rRnd, rArgs, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8,
      h.r9, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [rSig, rScr, h.a0, h.a1]
  simp only [slay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, h.a1, e1, e2]

/-- The body of the frame. -/
theorem signBody_tr {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m _ => SOk p L m)
      (.seq (muHash p (.slotOff fKey 64)) (callA n c (signArgs p))) fun _ _ => True := by
  have hE := oE_lt hp
  have mh := muHash_tr (I := signI p) (Φ := fun L m _ => SOk p L m) hE (fun _ _ _ h => h.facts.e)
    (tr := .slotOff fKey 64) (by decide) (fun L => L.key + BitVec.ofNat 64 64)
    (fun L g mx m t hc => by rw [hc.slotOff, fKey, hc.pKey])
    fun L hL => by
      have := hL.hKey
      have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
      exact ⟨⟨_, List.mem_append_left _ hL.inKey, w⟩,
        (hL.xKey.symm.sub_left w.sub).sub_right (Region.sub_prefix (by decide : 200 ≤ 1024)),
        (hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)),
        (hL.kKey.sub_left (Region.sub_prefix (by decide : 32 ≤ 104))).sub_right w.sub⟩
  have mh' := two_wp (I := signI p) (Φ := fun L m _ => SOk p L m) (Ψ := fun L m t => SOk p L m ∧ MuOk L m t) mh
    fun L g mx m₀ t hL hc hφ => by
      have := hL.hKey
      have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
      refine WP.mono (muHash_ok hL hφ.facts.e hc (tr := .slotOff fKey 64) (by decide)
        (fun t' hc' => by rw [hc'.slotOff, fKey, hc'.pKey]) ⟨_, List.mem_append_left _ hL.inKey, w⟩
        ((hL.xKey.symm.sub_left w.sub).sub_right (Region.sub_prefix (by decide : 200 ≤ 1024)))
        ((hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)))
        ((hL.kKey.sub_left (Region.sub_prefix (by decide : 32 ≤ 104))).sub_right w.sub))
        fun t' ⟨hc', _, hμ⟩ => ⟨hc', hφ, ?_⟩
      unfold MuOk
      rw [hμ, hc.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)]
  exact mh'.seq (signCall_tr hS hp)

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (p : Params) (x y : State) : Prop :=
  (signMessageContract p X86_64.abi 104).pre x ∧ (signMessageContract p X86_64.abi 104).pre y ∧
    (signMessageContract p X86_64.abi 104).pub x y

/-- After `cmp`. -/
abbrev ACmp (x x1 : State) : Prop :=
  x1.gpr = x.gpr ∧ x1.mem = x.mem ∧ x1.rd = x.rd ∧ x1.wr = x.wr ∧ x1.mxcsr = x.mxcsr ∧
    isa.eval .b x1 = some (decide ((x.gpr .r8).toNat < 256))

/-- After the moves before the push. -/
abbrev AMov (x x2 : State) : Prop :=
  (x.gpr .r8).toNat < 256 ∧ ((x2.gpr .r10 = stackArg x 0 ∧ x2.gpr .r11 = stackArg x 1 ∧ x2.gpr .rax = 0 ∧
    x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧ (∀ r, r ∉ [Reg.r10, .r11, .rax] → x2.gpr r = x.gpr r) ∧
    x2.rd = x.rd ∧ x2.wr = x.wr)

theorem spOnly_nomem {i : Instr} (h : ∀ s, isa.addrs i s = []) (hc : Taint.clobbers i .rsp = false) : SpOnly i :=
  ⟨fun s₁ s₂ _ => by rw [h, h], hc⟩

theorem signMessage_ct {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    ConstantTime isa (signMessageContract p X86_64.abi 104).pre (signMessageContract p X86_64.abi 104).pub
      (signMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (signMessageContract p X86_64.abi 104).pre s₁ ∧
      (signMessageContract p X86_64.abi 104).pre s₂ ∧ (signMessageContract p X86_64.abi 104).pub s₁ s₂) =
      Ghost (SP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `cmp r8, 256`.
  have hcmp := ghost_step (P := SP2 p) (A := fun x a => a = x) (B := ACmp) (c := .block [.alu .cmp .r8 (.imm 256)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (sPub_of hxy.2.2).rsp)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨cmp_ok _, cmp_ok _⟩
  refine RelCT.seq hcmp (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.2.2.2.2, f₂.2.2.2.2.2, (sPub_of hxy.2.2).r8]) ?_ ?_)
  · -- `ctx_len < 256`.
    have hmov := ghost_step (P := SP2 p) (A := fun x a => ACmp x a ∧ (x.gpr .r8).toNat < 256) (B := AMov)
      (c := .block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)])
      (block_rsp_tr (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact spOnly_nomem (fun _ => rfl) rfl)
        fun a b ⟨x, y, hxy, f₁, f₂⟩ => by rw [f₁.1.1, f₂.1.1]; exact (sPub_of hxy.2.2).rsp)
      fun x y a b hxy f₁ f₂ => by
        have mv : ∀ {x a : State}, (signMessageContract p X86_64.abi 104).pre x → ACmp x a →
            (x.gpr .r8).toNat < 256 → WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)),
              .mov32 .rax (.imm 0)]) a (AMov x) := fun hx f h8 =>
          WP.mono (signMov_ok (sPre_of hx) f.1 f.2.1 f.2.2.1) fun x2 ⟨h, k⟩ =>
            ⟨h8, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans f.2.2.2.2.1⟩,
              fun r hr => (k.gpr hr).trans (by rw [f.1]), k.2.1.trans f.2.2.1, k.2.2.trans f.2.2.2.1⟩
        exact ⟨mv hxy.1 f₁.1 f₁.2, mv hxy.2.1 f₂.1 f₂.2⟩
    refine RelCT.seq (RelCT.mono hmov (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, ?_⟩, ⟨f₂, ?_⟩⟩)
      fun _ _ h => h) ?_
    · rw [f₁.2.2.2.2.2] at hc; simpa using hc
    · rw [f₁.2.2.2.2.2, (sPub_of hxy.2.2).r8, ← f₂.2.2.2.2.2] at hc
      rw [f₂.2.2.2.2.2] at hc; simpa using hc
    refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
      rw [f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide)]; exact (sPub_of hxy.2.2).rsp) ?_
    -- The frame's body, from the push.
    let A : State → State → Prop := fun x a => ∃ s₁, AMov x s₁ ∧ a = pushed signRegs s₁
    let B : State → State → Prop := fun x t => (x.gpr .r8).toNat < 256 ∧ Ctx (slay p x) x.gpr x.mxcsr x.mem t
    have hdr := ghost_step (P := SP2 p) (A := A) (B := B) (c := .block setHdr)
      (block_rsp_tr (fun i hi => by
          simp only [setHdr, List.mem_singleton] at hi; subst hi
          exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩)
        fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
          subst e₁ e₂
          rw [pushed_rsp, pushed_rsp, f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide), (sPub_of hxy.2.2).rsp])
      fun x y a b hxy fa fb => by
        have en : ∀ {x a : State}, (signMessageContract p X86_64.abi 104).pre x → A x a →
            WP isa (.block setHdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
          subst e
          have h := sPre_of hx
          have hL := slay_ok hp h f.1
          refine WP.mono (entry_ok hL rfl (by decide) (by rw [f.2.2.1 _ (by decide), slay_B])
            (f.2.2.2.1.trans rfl) (f.2.2.2.2.trans rfl) (signRegs_vals f.2.2.1 f.2.1.1 f.2.1.2.1 f.2.1.2.2.1)
            (f.2.2.1 _ (by decide))) fun t ⟨hc, _, _⟩ =>
            ⟨f.1, hc.congr (fun r hr _ => f.2.2.1 r (cs_tmp r hr)) f.2.1.2.2.2.2 f.2.1.2.2.2.1⟩
        exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hdr (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
      ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ⟨h8x, ca⟩, ⟨h8y, cb⟩⟩ => ?_)
      (signBody_tr hS hp)
    have hx := sPre_of hxy.1
    have hy := sPre_of hxy.2.1
    have hpub := sPub_of hxy.2.2
    have e := slay_eq hx hy hpub
    refine ⟨slay p x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, slay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, rfl⟩, ⟨y, hy, h8y, e.symm, rfl⟩⟩
    have lk := hpub.leak
    rw [← hpub.rdi, ← hpub.rsi, ← hpub.rdx, ← hpub.rcx, ← hpub.r8, ← hpub.r9] at lk
    exact lk
  · exact block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ => by rw [f₁.1, f₂.1]; exact (sPub_of hxy.2.2).rsp

end

end VG.Proof.MlDsa.X86_64.Message

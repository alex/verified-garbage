import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Rel
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Hash

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: SHAKE256 leaks only the layout

Untrusted: everything here is checked by Lean. Two runs (`Two`) of the
zeroing of the Keccak state and of the calls of the sponge functions, whose
arguments are the same in both runs (functions of the layout), leak the
same (`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`); and so do `muHash` and
`trHash` (`muHash_tr`, `trHash_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlKem.X86_64 (Keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth)
open VG.Spec.MlDsa (Params)

section
variable {p : Params} {I : Lay → Mem → Mem → Prop}

/-- The 1 KiB of the external functions is where the code of `p` puts it. -/
abbrev EOk (p : Params) (L : Lay) : Prop := oE p = L.E

/-! ## Zeroing the state -/

theorem zeroSt_tr {Φ : Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → EOk p L) :
    RelCT isa (Two I Φ) (zeroSt p) fun _ _ => True := by
  have h1 := two_wp (I := I) (Φ := Φ) (Ψ := fun L _ t => t.gpr .rdi = L.ST) (c := .block ((aSt p).mov .rdi))
    (block_rsp_tr (arg_spOnly .rdi (by decide) _) fun _ _ h => h.rsp) fun L g mx m₀ t hL hc hφ => by
      have hok : (aSt p).ok = true := by
        simp only [Impl.MlDsa.X86_64.Message.aSt, Arg.ok, fScr, Bool.and_eq_true, decide_eq_true_eq]
        have := hL.hE; rw [hΦ L m₀ t hφ]; omega
      refine WP.mono (Arg.mov_ok .rdi (aSt p) hok (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ =>
        ⟨hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
          simp only [List.mem_singleton]; exact ne_cs hr (by decide)), by rw [h1, hc.aSt p (hΦ L m₀ t hφ)]⟩
  refine RelCT.seq h1 (RelCT.taint (A := taint) (Taint.ofRegs [.rsp, .rdi]) (fun a b hab => ?_) (by taint_decide))
  obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, f₁, f₂⟩ := hab
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [c₁.rsp, c₂.rsp]
  · rw [f₁, f₂]

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, after the moves. -/
theorem kabsArgs {L : Lay} (hL : L.Ok) (hE : EOk p L) {g mx m₀} {t t1 : State} (hc : Ctx L g mx m₀ t)
    {src len pos : Arg} (hm : Moved (absArgs p src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : Region.Disjoint ⟨L.B, 32⟩ ⟨dp, n⟩) :
    AbsorbArgs t1 L.ST dp L.KS 136 q n := by
  have hc1 : Ctx L g mx m₀ t1 := hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hm.1.1
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  exact ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, st_ks, dS, dK, k16 hc1 (k_st hL), k16 hc1 kD,
    k16 hc1 (k_ks hL)⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → EOk p L) {src len pos : Arg}
    (hok : (absArgs p src len pos).all Arg.ok = true) (dp : Lay → Addr) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g mx m (t : State), L.Ok → Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 32⟩ ⟨dp L, n L⟩) :
    RelCT isa (Two I Φ) (kabs p src len pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      Moved (absArgs p src len pos) t t1 → AbsorbArgs t1 L.ST (dp L) L.KS 136 (q L) (n L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L hL
      exact kabsArgs hL (hΦ L m₀ t hφ) hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine call_tr hok Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => absorb_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L hL => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L hL
    obtain ⟨R, hR, hX⟩ := hL.inX
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨R, hR, w_st.trans hX⟩, ⟨R, hR, w_ks.trans hX⟩]

theorem kpad_tr {Φ : Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → EOk p L) {pos : Arg}
    (hok : (padArgs p pos).all Arg.ok = true) (q : Lay → Nat)
    (hv : ∀ (L : Lay) g mx m (t : State), L.Ok → Ctx L g mx m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136) :
    RelCT isa (Two I Φ) (kpad p pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      Moved (padArgs p pos) t t1 → PadArgs t1 L.ST L.KS 136 (q L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      have hc1 : Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
      obtain ⟨e1, e2, e3, _, e5⟩ := argsIn5 hm.1.1
      rw [hc.aSt p (hΦ L m₀ t hφ)] at e1
      rw [hc.aKs p (hΦ L m₀ t hφ)] at e5
      rw [hv L g mx m₀ t hL hc hφ] at e3
      exact ⟨e1, e2, e3, e5, by decide, hs L hL, st_ks, k16 hc1 (k_st hL), k16 hc1 (k_ks hL)⟩
  refine call_tr hok Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => pad_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L hL => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.r8, y.rdi, y.rsi, y.rdx, y.r8,
      f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs), c₁.rsp, c₂.rsp,
      and_self]
  · obtain ⟨R, hR, hX⟩ := hL.inX
    refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨R, hR, w_st.trans hX⟩, ⟨R, hR, w_ks.trans hX⟩]

theorem ksqz_tr {Φ : Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → EOk p L)
    (hok : (sqzArgs p).all Arg.ok = true) :
    RelCT isa (Two I Φ) (ksqz p) fun _ _ => True := by
  have args : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      Moved (sqzArgs p) t t1 → SqueezeArgs t1 L.ST L.MU L.KS 136 0 64 :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      have hc1 : Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hm.1.1
      rw [hc.aSt p (hΦ L m₀ t hφ)] at e1
      rw [hc.aKs p (hΦ L m₀ t hφ)] at e6
      rw [hc.aMu p (hΦ L m₀ t hφ)] at e4
      exact ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, st_mu, st_ks, mu_ks, k16 hc1 (k_st hL),
        k16 hc1 (k_mu hL), k16 hc1 (k_ks hL)⟩
  refine call_tr hok Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => squeeze_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L hL => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.squeezeX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · obtain ⟨R, hR, hX⟩ := hL.inX
    refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨R, hR, w_st.trans hX⟩, ⟨R, hR, w_mu.trans hX⟩, ⟨R, hR, w_ks.trans hX⟩]

/-! ## `μ` and `tr` -/

/-- Where the two bytes of the formatted message are. -/
theorem hdrSide {L : Lay} (hL : L.Ok) : 64 < 136 ∧ 2 < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP, 2⟩ R) ∧
    Region.Disjoint ⟨L.SP, 2⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.SP, 2⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 32⟩ ⟨L.SP, 2⟩ :=
  ⟨by decide, by decide, ⟨L.FR, by simp, within_base _ (by decide)⟩,
    by have := hL.stk_x (d := 32) (n := 2) (e := 0) (k := 200) (by decide) (by decide); simpa only [x0] using this,
    hL.stk_x (d := 32) (n := 2) (by decide) (by decide), Offset.base_disjoint _ (by decide) (by decide)⟩

/-- Where the context string is. -/
theorem ctxSide {L : Lay} (hL : L.Ok) : 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R) ∧
    Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 32⟩ ⟨L.ctx, L.ctxLen.toNat⟩ :=
  ⟨by decide, L.ctxLen.isLt, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
    by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
    (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm,
    hL.kCtx.sub_left (Region.sub_prefix (by decide))⟩

/-- Where the message is. -/
theorem msgSide {L : Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ L.len.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.msg, L.len.toNat⟩ R) ∧
    Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 32⟩ ⟨L.msg, L.len.toNat⟩ :=
  ⟨hq, L.len.isLt, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
    by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
    (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm,
    hL.kMsg.sub_left (Region.sub_prefix (by decide))⟩

theorem absOk' (hE : oE p + 1024 < 2 ^ 31) {src len pos : Arg} (h1 : src.ok = true) (h2 : len.ok = true)
    (h3 : pos.ok = true) : (absArgs p src len pos).all Arg.ok = true := by
  simp only [absArgs, List.all_cons, List.all_nil, h1, h2, h3, Bool.and_true, Bool.true_and]
  simp only [Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, Arg.ok, fScr, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

/-- The position after the context string. -/
abbrev qCtx (L : Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : Lay) : Nat := (qCtx L + L.len.toNat) % 136

theorem muHash_tr (hE : oE p + 1024 < 2 ^ 31) {Φ : Lay → Mem → State → Prop}
    (hΦ : ∀ L m t, Φ L m t → EOk p L) {tr : Arg} (hok : tr.ok = true) (trp : Lay → Addr)
    (htr : ∀ (L : Lay) g mx m (t : State), Ctx L g mx m t → tr.val t = trp L)
    (hs : ∀ L : Lay, L.Ok → (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨trp L, 64⟩ R) ∧
      Region.Disjoint ⟨trp L, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨trp L, 64⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 32⟩ ⟨trp L, 64⟩) :
    RelCT isa (Two I Φ) (muHash p tr) fun _ _ => True := by
  -- The relation keeps only `EOk` and the position in `rax`.
  let Ψ : (Lay → Nat) → Lay → Mem → State → Prop := fun q L _ t => EOk p L ∧ (t.gpr .rax).toNat = q L
  have z := two_wp (I := I) (Ψ := fun L _ _ => EOk p L) (zeroSt_tr hΦ)
    fun L g mx m₀ t hL hc hφ => WP.mono (zeroSt_ok hL (hΦ L m₀ t hφ) hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (kabs_tr (Φ := fun L _ _ => EOk p L) (fun _ _ _ h => h) (absOk' hE hok rfl rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g mx m t _ hc _ => ⟨htr L g mx m t hc, rfl, rfl⟩)
      fun L hL => ⟨by decide, by decide, (hs L hL).1, (hs L hL).2.1, (hs L hL).2.2.1, (hs L hL).2.2.2⟩)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d⟩ := hs L hL
      exact WP.mono (kabs_ok hL hφ hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (absOk' hE hok rfl rfl) (htr L g mx m₀ t hc) rfl rfl (by decide)
        (by decide) a b c d) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ, hx⟩
  have a2 := two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (kabs_tr (src := .sp) (len := .imm 2) (pos := .imm 64) (fun _ _ _ h => h.1) (absOk' hE rfl rfl rfl) (fun L => L.SP) (fun _ => 2) (fun _ => 64)
      (fun L g mx m t _ hc _ => ⟨hc.rsp, rfl, rfl⟩) fun L hL => hdrSide hL)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := hdrSide hL
      exact WP.mono (kabs_ok hL hφ.1 hc (src := .sp) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (absOk' hE rfl rfl rfl) hc.rsp rfl rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ.1, hx⟩
  have a3 := two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ qCtx)
    (kabs_tr (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (fun _ _ _ h => h.1)
      (absOk' hE (by decide) (by decide) (by decide)) (fun L => L.ctx)
      (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g mx m t _ hc _ => ⟨by rw [hc.slot, fCtx, hc.pCtx], by rw [hc.slot, fCtxLen, hc.pCtxLen,
        ofNat_toNat_self], rfl⟩) fun L hL => ctxSide hL)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := ctxSide hL
      exact WP.mono (kabs_ok hL hφ.1 hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (absOk' hE (by decide) (by decide) (by decide))
        (by rw [hc.slot, fCtx, hc.pCtx]) (by rw [hc.slot, fCtxLen, hc.pCtxLen, ofNat_toNat_self]) rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ.1, hx⟩
  have a4 := two_wp (I := I) (Φ := Ψ qCtx) (Ψ := Ψ qMsg)
    (kabs_tr (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (fun _ _ _ h => h.1)
      (absOk' hE (by decide) (by decide) rfl) (fun L => L.msg)
      (fun L => L.len.toNat) qCtx
      (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot, fMsg, hc.pMsg], by rw [hc.slot, fLen, hc.pLen,
        ofNat_toNat_self], ofNat_toNat_eq hφ.2⟩) fun L hL => msgSide hL (Nat.mod_lt _ (by decide)))
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := msgSide hL (Nat.mod_lt (66 + L.ctxLen.toNat) (by decide : 136 > 0))
      exact WP.mono (kabs_ok hL hφ.1 hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (absOk' hE (by decide) (by decide) rfl)
        (by rw [hc.slot, fMsg, hc.pMsg]) (by rw [hc.slot, fLen, hc.pLen, ofNat_toNat_self])
        (ofNat_toNat_eq hφ.2) a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hφ.1, hx⟩
  have pd := kpad_tr (I := I) (Φ := Ψ qMsg) (fun _ _ _ h => h.1) (pos := .ret) (by
      simp only [padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, true_and]
      omega) qMsg (fun L g mx m t _ _ hφ => ofNat_toNat_eq hφ.2) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := Ψ qMsg) (Ψ := fun L _ _ => EOk p L) pd
    fun L g mx m₀ t hL hc hφ => WP.mono (kpad_ok hL hφ.1 hc (pos := .ret) (by
      simp only [padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, true_and]
      omega) (ofNat_toNat_eq hφ.2) (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', hφ.1⟩
  have sq := ksqz_tr (I := I) (Φ := fun L _ _ => EOk p L) (fun _ _ _ h => h) (by
    simp only [sqzArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aMu,
      Impl.MlDsa.X86_64.Message.aKs, List.all_cons, List.all_nil, Arg.ok, fScr, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    omega)
  exact RelCT.seq (RelCT.mono z (fun a b h => h) fun _ _ h => h)
    (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq sq)))))

theorem trHash_tr (hE : oE p + 1024 < 2 ^ 31) (hk : p.pkLen < 2 ^ 31) {Φ : Lay → Mem → State → Prop}
    (hΦ : ∀ L m t, Φ L m t → EOk p L ∧ L.keyLen = p.pkLen) :
    RelCT isa (Two I Φ) (trHash p) fun _ _ => True := by
  have keySide : ∀ L : Lay, L.Ok → 0 < 136 ∧ L.keyLen < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.key, L.keyLen⟩ R) ∧
      Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 32⟩ ⟨L.key, L.keyLen⟩ := fun L hL =>
    ⟨by decide, by have := hL.hKey; omega, ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by decide)).symm,
      hL.kKey.sub_left (Region.sub_prefix (by decide))⟩
  have z := two_wp (I := I) (Ψ := fun L _ _ => EOk p L ∧ L.keyLen = p.pkLen)
    (zeroSt_tr fun L m t h => (hΦ L m t h).1)
    fun L g mx m₀ t hL hc hφ => WP.mono (zeroSt_ok hL (hΦ L m₀ t hφ).1 hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := two_wp (I := I) (Φ := fun L _ _ => EOk p L ∧ L.keyLen = p.pkLen) (Ψ := fun L _ _ => EOk p L)
    (kabs_tr (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0) (fun _ _ _ h => h.1)
      (absOk' hE (by decide) (by simp [Arg.ok]; omega) rfl) (fun L => L.key) (fun L => L.keyLen) (fun _ => 0)
      (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot, fKey, hc.pKey], by rw [hφ.2]; rfl, rfl⟩) keySide)
    fun L g mx m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := keySide L hL
      exact WP.mono (kabs_ok hL hφ.1 hc (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
        (n := L.keyLen) (q := 0) (absOk' hE (by decide) (by simp [Arg.ok]; omega) rfl)
        (by rw [hc.slot, fKey, hc.pKey]) (by rw [hφ.2]; rfl) rfl a b c d e f)
        fun t' ⟨hc', _⟩ => ⟨hc', hφ.1⟩
  have pd := kpad_tr (I := I) (Φ := fun L _ _ => EOk p L) (fun _ _ _ h => h) (pos := .imm (p.pkLen % 136)) (by
      simp only [padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      omega) (fun _ => p.pkLen % 136) (fun _ _ _ _ _ _ _ _ => rfl) fun _ _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := fun L _ _ => EOk p L) (Ψ := fun L _ _ => EOk p L) pd
    fun L g mx m₀ t hL hc hφ => WP.mono (kpad_ok hL hφ hc (pos := .imm (p.pkLen % 136)) (by
      simp only [padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      omega) rfl (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', hφ⟩
  have sq := ksqz_tr (I := I) (Φ := fun L _ _ => EOk p L) (fun _ _ _ h => h) (by
    simp only [sqzArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aMu,
      Impl.MlDsa.X86_64.Message.aKs, List.all_cons, List.all_nil, Arg.ok, fScr, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    omega)
  exact RelCT.seq (RelCT.mono z (fun a b h => h) fun _ _ h => h) (a1.seq (pd'.seq sq))

end

end VG.Proof.MlDsa.X86_64.Message

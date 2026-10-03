import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Rel
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash

/-!
# Ed448 verification on x86-64: the hash leaks only the layout

Two runs (`Two`) of the zeroing of the Keccak state and of the calls of the
sponge functions, whose arguments are the same in both runs (functions of
the layout), leak the same (`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`);
and so does `hash` (`hash_tr`), each absorption starting at the position the
previous one returned, a function of the lengths.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre)

section
variable {I : Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zhead_ok {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) :
    WP isa (.block [.mov .rdi (.mem (stk fScr)), .mov32 .rax (.imm 0)]) t fun t2 =>
      Ctx L g mx m₀ t2 ∧ t2.gpr .rdi = L.ST := by
  show WP isa (.block (aSt.mov .rdi ++ [.mov32 .rax (.imm 0)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (Arg.mov_ok .rdi aSt (by decide) (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hx2⟩, k2⟩ => ?_
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
    simp only [List.mem_singleton]; exact ne_cs hr (by decide))
  exact ⟨hc1.regs k2.2.1 k2.2.2 hm2 hx2 fun r hr => k2.gpr (by
    simp only [List.mem_singleton]; exact ne_cs hr (by decide)), (k2.gpr (by decide)).trans (h1.trans hc.aSt)⟩

theorem zeroSt_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) zeroSt fun _ _ => True := by
  have h1 := two_wp (I := I) (Φ := Φ) (Ψ := fun L _ t => t.gpr .rdi = L.ST)
    (c := .block [.mov .rdi (.mem (stk fScr)), .mov32 .rax (.imm 0)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
        · exact spOnly_nomem (fun _ => rfl) rfl) fun _ _ h => h.rsp)
    fun _ _ _ _ _ _ hc _ => zhead_ok hc
  refine RelCT.seq h1 (RelCT.taint (A := taint) (Taint.ofRegs [.rsp, .rdi]) (fun a b hab => ?_) (by taint_decide))
  obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, f₁, f₂⟩ := hab
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [c₁.rsp, c₂.rsp]
  · rw [f₁, f₂]

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, after the moves. -/
theorem kabsArgs {L : Lay} (hL : L.Ok) {g mx m₀} {t t1 : State} (hc : Ctx L g mx m₀ t)
    {src len pos : Arg} (hm : Moved (absArgs src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨dp, n⟩) :
    AbsorbArgs t1 L.ST dp L.KS 136 q n := by
  have hc1 : Ctx L g mx m₀ t1 := hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hm.1.1
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  exact ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, st_ks L, dS, dK, k16 hc1 (k_st hL), k16 hc1 kD,
    k16 hc1 (k_ks hL)⟩

theorem w_scr {L : Lay} (hL : L.Ok) {r : Region} (h : Within r L.SCR) : ∃ R ∈ L.FR :: L.wr, Within r R :=
  ⟨L.SCR, by simp [hL.wr], h⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : (absArgs src len pos).all Arg.ok = true) (dp : Lay → Addr) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g mx m (t : State), L.Ok → Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 16⟩ ⟨dp L, n L⟩) :
    RelCT isa (Two I Φ) (kabs src len pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      Moved (absArgs src len pos) t t1 → AbsorbArgs t1 L.ST (dp L) L.KS 136 (q L) (n L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L hL
      exact kabsArgs hL hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine call_tr hok Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => absorb_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L hL
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [w_scr hL w_st, w_scr hL w_ks]

/-- The position in `rax`, a function of the layout. -/
abbrev Pos (q : Lay → Nat) : Lay → Mem → State → Prop := fun L _ t => (t.gpr .rax).toNat = q L

/-- An absorption, with the position it returns. -/
theorem kabs_two {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : (absArgs src len pos).all Arg.ok = true) (dp : Lay → Addr) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g mx m (t : State), L.Ok → Ctx L g mx m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      Region.Disjoint ⟨L.B, 16⟩ ⟨dp L, n L⟩) :
    RelCT isa (Two I Φ) (kabs src len pos) (Two I (Pos fun L => (q L + n L) % 136)) :=
  two_wp (kabs_tr hok dp n q hv hs) fun L g mx m₀ t hL hc hφ => by
    obtain ⟨h1, h2, h3⟩ := hv L g mx m₀ t hL hc hφ
    obtain ⟨a, b, c, d, e, f⟩ := hs L hL
    exact WP.mono (kabs_ok hL hc hok h1 h2 h3 a b c d e f) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩

theorem kpad_tr {Φ : Lay → Mem → State → Prop} {pos : Arg}
    (hok : (padArgs pos).all Arg.ok = true) (q : Lay → Nat)
    (hv : ∀ (L : Lay) g mx m (t : State), L.Ok → Ctx L g mx m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136) :
    RelCT isa (Two I Φ) (kpad pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      Moved (padArgs pos) t t1 → PadArgs t1 L.ST L.KS 136 (q L) :=
    fun L g mx m₀ t t1 hL hc hφ hm => by
      have hc1 : Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
      obtain ⟨e1, e2, e3, _, e5⟩ := argsIn5 hm.1.1
      rw [hc.aSt] at e1
      rw [hc.aKs] at e5
      rw [hv L g mx m₀ t hL hc hφ] at e3
      exact ⟨e1, e2, e3, e5, by decide, hs L hL, st_ks L, k16 hc1 (k_st hL), k16 hc1 (k_ks hL)⟩
  refine call_tr hok Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => pad_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.r8, y.rdi, y.rsi, y.rdx, y.r8,
      f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs), c₁.rsp, c₂.rsp,
      and_self]
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [w_scr hL w_st, w_scr hL w_ks]

theorem ksqz_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) ksqz fun _ _ => True := by
  have args : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      Moved sqzArgs t t1 → SqueezeArgs t1 L.ST L.H L.KS 136 0 114 :=
    fun L g mx m₀ t t1 hL hc _ hm => by
      have hc1 : Ctx L g mx m₀ t1 :=
        hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hm.1.1
      rw [hc.aSt] at e1
      rw [hc.aKs] at e6
      rw [hc.sp] at e4
      exact ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, st_h hL, st_ks L, h_ks hL,
        k16 hc1 (k_st hL), k16 hc1 k_h, k16 hc1 (k_ks hL)⟩
  refine call_tr (by decide) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩])
    (fun L g mx m₀ t t1 hL hc hφ hm => squeeze_pre (args L g mx m₀ t t1 hL hc hφ hm))
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.squeezeX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), rsp_ce, x.rdi, x.rsi, x.rdx, x.rcx, x.r8, x.r9, y.rdi, y.rsi,
      y.rdx, y.rcx, y.r8, y.r9, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs), f₂.2.gpr (by decide : Reg.rsp ∉ argRegs),
      c₁.rsp, c₂.rsp, and_self]
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [w_scr hL w_st, ⟨L.FR, by simp, w_h.trans (within_base _ (by decide))⟩, w_scr hL w_ks]

/-! ## The hash -/

/-- Where each piece absorbed is. -/
theorem hdrSide {L : Lay} (hL : L.Ok) : 0 < 136 ∧ 10 < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP, 10⟩ R) ∧
    Region.Disjoint ⟨L.SP, 10⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.SP, 10⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.SP, 10⟩ :=
  ⟨by decide, by decide, ⟨L.FR, by simp, within_base _ (by decide)⟩,
    by have := hL.stk_x (d := 16) (n := 10) (e := 0) (k := 200) (by decide) (by decide); simpa only [x0] using this,
    hL.stk_x (d := 16) (n := 10) (by decide) (by decide), Offset.base_disjoint _ (by decide) (by decide)⟩

theorem ctxSide {L : Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ L.ctxLen.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R) ∧
    Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.ctx, L.ctxLen.toNat⟩ :=
  ⟨hq, L.ctxLen.isLt, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
    by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
    (hL.x_r hL.xCtx (e := 256) (k := 640) (by decide)).symm, k_r hL hL.kCtx⟩

theorem sigSide {L : Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ 57 < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.sig, 57⟩ R) ∧
    Region.Disjoint ⟨L.sig, 57⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.sig, 57⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.sig, 57⟩ :=
  have xR := hL.xSig.sub_right r57_sub
  ⟨hq, by decide, ⟨L.SIG, List.mem_append_left _ hL.inSig, within_base _ (by decide)⟩,
    by have := hL.x_r xR (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
    (hL.x_r xR (e := 256) (k := 640) (by decide)).symm, k_r hL (hL.kSig.sub_right r57_sub)⟩

theorem pkSide {L : Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ 57 < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.pk, 57⟩ R) ∧
    Region.Disjoint ⟨L.pk, 57⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.pk, 57⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.pk, 57⟩ :=
  ⟨hq, by decide, ⟨L.PK, List.mem_append_left _ hL.inPk, within_self _⟩,
    by have := hL.x_r hL.xPk (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
    (hL.x_r hL.xPk (e := 256) (k := 640) (by decide)).symm, k_r hL hL.kPk⟩

theorem msgSide {L : Lay} (hL : L.Ok) {q : Nat} (hq : q < 136) : q < 136 ∧ L.len.toNat < 2 ^ 64 ∧
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.msg, L.len.toNat⟩ R) ∧
    Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.msg, L.len.toNat⟩ :=
  ⟨hq, L.len.isLt, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
    by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
    (hL.x_r hL.xMsg (e := 256) (k := 640) (by decide)).symm, k_r hL hL.kMsg⟩

/-- The positions after the header, the context, `R`, `A` and the message. -/
abbrev qH (_ : Lay) : Nat := (0 + 10) % 136
abbrev qC (L : Lay) : Nat := (qH L + L.ctxLen.toNat) % 136
abbrev qR (L : Lay) : Nat := (qC L + 57) % 136
abbrev qA (L : Lay) : Nat := (qR L + 57) % 136
abbrev qM (L : Lay) : Nat := (qA L + L.len.toNat) % 136

theorem slotLen {L : Lay} {g mx m} {t : State} (hc : Ctx L g mx m t) {f : Nat} {x : BitVec 64}
    (h : t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 = x) : (Arg.slot f).val t = BitVec.ofNat 64 x.toNat := by
  rw [hc.slot, h, ofNat_toNat_self]

theorem hash_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) hash fun _ _ => True := by
  have z := two_wp (I := I) (Φ := Φ) (Ψ := fun _ _ _ => True) zeroSt_tr
    fun L g mx m₀ t hL hc _ => WP.mono (zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have a1 := kabs_two (I := I) (Φ := fun _ _ _ => True) (src := .sp fHdr) (len := .imm 10) (pos := .imm 0)
    (by decide) (fun L => L.SP) (fun _ => 10) (fun _ => 0)
    (fun L g mx m t _ hc _ => ⟨by rw [hc.sp]; exact x0 _, rfl, rfl⟩) fun L hL => hdrSide hL
  have a2 := kabs_two (I := I) (Φ := Pos qH) (src := .slot fCtx) (len := .slot fCtxLen) (pos := .ret)
    (by decide) (fun L => L.ctx) (fun L => L.ctxLen.toNat) qH
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pCtx, slotLen hc hc.pCtxLen, ofNat_toNat_eq hφ⟩)
    fun L hL => ctxSide hL (show (0 + 10) % 136 < 136 by decide)
  have a3 := kabs_two (I := I) (Φ := Pos qC) (src := .slot fSig) (len := .imm 57) (pos := .ret)
    (by decide) (fun L => L.sig) (fun _ => 57) qC
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pSig, rfl, ofNat_toNat_eq hφ⟩)
    fun L hL => sigSide hL (Nat.mod_lt _ (by decide))
  have a4 := kabs_two (I := I) (Φ := Pos qR) (src := .slot fPk) (len := .imm 57) (pos := .ret)
    (by decide) (fun L => L.pk) (fun _ => 57) qR
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pPk, rfl, ofNat_toNat_eq hφ⟩)
    fun L hL => pkSide hL (Nat.mod_lt _ (by decide))
  have a5 := kabs_two (I := I) (Φ := Pos qA) (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
    (by decide) (fun L => L.msg) (fun L => L.len.toNat) qA
    (fun L g mx m t _ hc hφ => ⟨by rw [hc.slot]; exact hc.pMsg, slotLen hc hc.pLen, ofNat_toNat_eq hφ⟩)
    fun L hL => msgSide hL (Nat.mod_lt _ (by decide))
  have pd := two_wp (I := I) (Φ := Pos qM) (Ψ := fun _ _ _ => True)
    (kpad_tr (pos := .ret) (by decide) qM (fun _ _ _ _ _ _ _ hφ => ofNat_toNat_eq hφ)
      fun _ _ => Nat.mod_lt _ (by decide))
    fun L g mx m₀ t hL hc hφ => WP.mono (kpad_ok hL hc (pos := .ret) (by decide) (ofNat_toNat_eq hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (a5.seq (pd.seq ksqz_tr))))))

end

end VG.Proof.Ed448.X86_64.Verify

import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Args
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Keccak
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. Between the frame's push and
pop (`Ctx`): zeroing the Keccak state at `X` (`zeroSt_ok`), and the calls of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` on it, with
their working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`); then
`muHash`, which leaves `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840`
(`muHash_ok`), and `trHash`, which leaves `H(pk, 64)` there (`trHash_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth callEntry_repr callEntry_bytesAt callEntry_stateAt
  ofNat_toNat' rate_lt)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)
open VG.Spec.MlDsa (Params)

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {p : Params}

/-- The 16 bytes below `rsp` that a sponge function's call uses are in the
32 bytes below the frame. -/
theorem k16 {t : State} (hc : Ctx L g mx m₀ t) {r : Region} (h : Region.Disjoint ⟨L.B, 32⟩ r) :
    (below (t.gpr .rsp) 16).Disjoint r := by
  rw [hc.rsp]; exact h.sub_left (below_call_sub L.B (by omega))

theorem x0 (L : Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _

theorem k32x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.B, 32⟩ ⟨L.X + BitVec.ofNat 64 e, k⟩ := by
  have := hL.stk_x (d := 0) (n := 32) (by omega) h₂
  simpa only [BitVec.add_zero] using this

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega) (by omega) (by omega)

theorem w_st : Within ⟨L.ST, 200⟩ L.XS := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.XS := within_off _ (by omega)
theorem w_mu : Within ⟨L.MU, 64⟩ L.XS := within_off _ (by omega)

theorem k_st (hL : L.Ok) : Region.Disjoint ⟨L.B, 32⟩ ⟨L.ST, 200⟩ := by
  have := k32x hL (e := 0) (k := 200) (by omega); simpa only [x0] using this
theorem k_ks (hL : L.Ok) : Region.Disjoint ⟨L.B, 32⟩ ⟨L.KS, 640⟩ := k32x hL (by omega)
theorem k_mu (hL : L.Ok) : Region.Disjoint ⟨L.B, 32⟩ ⟨L.MU, 64⟩ := k32x hL (by omega)

/-- The return address of a call from the frame, apart from what a region
apart from the 32 bytes below the frame. -/
theorem ret_of_k {r : Region} (h : Region.Disjoint ⟨L.B, 32⟩ r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 8⟩ r :=
  h.sub_left (Offset.sub_base _ (by omega))

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (zeroSt p) t fun t' => Ctx L g mx m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  have hok : (aSt p).ok = true := by
    simp only [Impl.MlDsa.X86_64.Message.aSt, Arg.ok, fScr, Bool.and_eq_true, decide_eq_true_eq]
    have := hL.hE; omega
  refine WP.seq (WP.mono (Arg.mov_ok .rdi (aSt p) hok (by decide) t hc.frOk)
    fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
    simp only [List.mem_singleton]; exact ne_cs hr (by decide))
  rw [hc.aSt p hE] at h1
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.gpr .rax = 0 ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hax, hx2⟩, k2⟩ => ?_
  have hdi : t2.gpr .rdi = L.ST := (k2.gpr (by decide)).trans h1
  have hw2 : t2.wr = L.FR :: L.wr := k2.2.2.trans hc1.wr
  obtain ⟨R, hR, hXR⟩ := hL.inX
  refine WP.mono_mx (by decide) (Proof.MlDsa.X86_64.Sign.zeroSt_ok .rdi 0 t2 hax fun i hi => ?_)
    fun t3 ⟨hz, hf, k3⟩ hx3 => ?_
  · rw [hw2, hdi, x0]
    obtain ⟨o, hb, hl⟩ := (within_off L.X (d := 8 * i) (n := 8) (k := 1024) (by omega)).trans hXR
    refine ⟨R, List.mem_cons_of_mem _ hR, ?_⟩
    simp only at hb
    rw [hb]
    exact Offset.contains_base _ hl (by have := hL.lenW R hR; simp only at hl; omega)
  · rw [hdi, x0] at hz hf
    rw [hm2] at hf
    have hcs : ∀ r ∈ calleeSaved, t3.gpr r = t1.gpr r := fun r hr => by
      rw [k3.gpr (by simp), k2.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide))]
    have hf' : Frame ([⟨L.ST, 200⟩] ++ [⟨L.B, 32⟩]) t1.mem t3.mem := hf.mono fun r hr => by simp at hr ⊢; exact .inl hr
    refine ⟨hc1.of_frame hL (k3.2.1.trans k2.2.1) (k3.2.2.trans k2.2.2) hcs
      (by rw [hx3, hx2]) hf' (by simpa using w_st), by rw [← hm1]; exact hf, hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (p : Params) (src len pos : Arg) : List Arg := [aSt p, .imm 136, pos, src, len, aKs p]

theorem kabs_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : Ctx L g mx m₀ t)
    {src len pos : Arg} (hok : (absArgs p src len pos).all Arg.ok = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 32⟩ ⟨dp, n⟩) :
    WP isa (kabs p src len pos) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 32⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem dp n)) ∧ (t'.gpr .rax).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q n :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, st_ks, dS, dK, k16 hc1 (k_st hL), k16 hc1 kD,
      k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp (by rw [absorb_depth]; decide)
    hc1 (absorb_pre ha) (by simpa using hin) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [w_st, w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩ => ?_
  have hn' := ofNat_toNat' hnl
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, hn', hq'] at hpost hrax
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_, by rw [← hg₂ _ (by decide)]; exact hrax⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rwa [callEntry_bytesAt t1 hnl ha.k_d, hm] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (p : Params) (pos : Arg) : List Arg := [aSt p, .imm 136, pos, .imm 0x1f, aKs p]

theorem kpad_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : Ctx L g mx m₀ t)
    {pos : Arg} (hok : (padArgs p pos).all Arg.ok = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad p pos) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 32⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e5
  rw [hq] at e3
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨e1, e2, e3, e5, by decide, hql, st_ks, k16 hc1 (k_st hL), k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp (by rw [pad_depth]; decide)
    hc1 (pad_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [w_st, w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂, hq'] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rw [this]
  rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs (p : Params) : List Arg := [aSt p, .imm 136, .imm 0, aMu p, .imm 64, aKs p]

theorem ksqz_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (ksqz p) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩, ⟨L.B, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = squeezeFrom 136 (stateAt t.mem L.ST) 0 64 := by
  have hok : (sqzArgs p).all Arg.ok = true := by
    simp only [sqzArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aMu,
      Impl.MlDsa.X86_64.Message.aKs, List.all_cons, List.all_nil, Arg.ok, fScr, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    have := hL.hE; omega
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt p hE] at e1
  rw [hc.aKs p hE] at e6
  rw [hc.aMu p hE] at e4
  have ha : SqueezeArgs t1 L.ST L.MU L.KS 136 0 64 :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, st_mu, st_ks, mu_ks, k16 hc1 (k_st hL),
      k16 hc1 (k_mu hL), k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]; decide) hc1 (squeeze_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [w_st, w_mu, w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost, _⟩ => ?_
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, Arg.val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  rw [hpost, callEntry_stateAt t1 ha.k_st, hm]

/-! ## `μ` -/

/-- The two bytes `0 ‖ ctx_len` of the formatted message. -/
abbrev hdrBytes (L : Lay) : List Byte := [0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- A frame of regions within `X` and the 32 bytes below the frame. -/
theorem frameX {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, r = ⟨L.B, 32⟩ ∨ Within r L.XS) : Frame [L.XS, ⟨L.B, 32⟩] m m' :=
  Frame.sub h fun r hr => by
    rcases hs r hr with rfl | hw
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, hw.sub⟩

theorem absOk (hL : L.Ok) (hE : oE p = L.E) {src len pos : Arg} (h1 : src.ok = true) (h2 : len.ok = true)
    (h3 : pos.ok = true) : (absArgs p src len pos).all Arg.ok = true := by
  have := hL.hE
  simp only [absArgs, List.all_cons, List.all_nil, h1, h2, h3, Bool.and_true, Bool.true_and]
  simp only [Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, Arg.ok, fScr, Bool.and_eq_true,
    decide_eq_true_eq, hE]
  omega

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; exact (ofNat_toNat_self x).symm

theorem muHash_ok (hL : L.Ok) (hE : oE p = L.E) {t : State} (hc : Ctx L g mx m₀ t)
    {tr : Arg} (hok : tr.ok = true) {trp : Addr}
    (htr : ∀ t', Ctx L g mx m₀ t' → tr.val t' = trp)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨trp, 64⟩ R)
    (dS : Region.Disjoint ⟨trp, 64⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨trp, 64⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 32⟩ ⟨trp, 64⟩) :
    WP isa (muHash p tr) t fun t' => Ctx L g mx m₀ t' ∧ Frame [L.XS, ⟨L.B, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt t.mem trp 64 ++ hdrBytes L ++
        bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.msg L.len.toNat) 64 := by
  have hctx := hL.ctxLt
  -- Zero the state.
  refine WP.seq (WP.mono (zeroSt_ok hL hE hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have etr : bytesAt t1.mem trp 64 = bytesAt t.mem trp 64 :=
    Proof.MlKem.bytesAt_congr fun i hi => hf1.bytes (R := ⟨trp, 64⟩) (by simpa using dS) (by show 64 ≤ 2 ^ 64; decide) hi
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  -- `tr`.
  refine WP.seq (WP.mono (kabs_ok hL hE hc1 (absOk hL hE hok rfl rfl) (htr t1 hc1) rfl rfl (by decide)
    (by decide) hin dS dK kD) fun t2 ⟨hc2, hf2, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, etr] at hR2
  -- `0 ‖ ctx_len`, from the frame.
  have hsp2 : Arg.sp.val t2 = L.SP := hc2.rsp
  have wfr : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP, 2⟩ R := ⟨L.FR, by simp, within_base _ (by omega)⟩
  have fS : Region.Disjoint ⟨L.SP, 2⟩ ⟨L.ST, 200⟩ := by
    have := hL.stk_x (d := 32) (n := 2) (e := 0) (k := 200) (by omega) (by omega); simpa only [x0] using this
  have fK : Region.Disjoint ⟨L.SP, 2⟩ ⟨L.KS, 640⟩ := hL.stk_x (d := 32) (n := 2) (by omega) (by omega)
  have kF : Region.Disjoint ⟨L.B, 32⟩ ⟨L.SP, 2⟩ := Offset.base_disjoint _ (by omega) (by omega)
  refine WP.seq (WP.mono (kabs_ok hL hE hc2 (absOk hL hE rfl rfl rfl) hsp2 rfl rfl (by decide) (by decide)
    wfr fS fK kF) fun t3 ⟨hc3, hf3, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by rw [Proof.MlKem.bytesAt_length])
  rw [hc2.hdr] at hR3
  -- The context string.
  have hcl : (Arg.slot fCtxLen).val t3 = BitVec.ofNat 64 L.ctxLen.toNat := by
    rw [hc3.slot, fCtxLen, hc3.pCtxLen, ofNat_toNat_self]
  have wc : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R :=
    ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩
  refine WP.seq (WP.mono (kabs_ok hL hE hc3 (absOk hL hE (by decide) (by decide) (by decide))
    (by rw [hc3.slot, fCtx, hc3.pCtx]) hcl rfl (by decide) (by omega) wc
    (by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xCtx (e := 200) (k := 640) (by omega)).symm
    (by have := hL.stk_r hL.kCtx (d := 0) (n := 32) (by omega); simpa only [BitVec.add_zero] using this))
    fun t4 ⟨hc4, hf4, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc3.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at hR4
  -- The message.
  have hln : (Arg.slot fLen).val t4 = BitVec.ofNat 64 L.len.toNat := by
    rw [hc4.slot, fLen, hc4.pLen, ofNat_toNat_self]
  have wm : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.msg, L.len.toNat⟩ R :=
    ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩
  refine WP.seq (WP.mono (kabs_ok hL hE hc4 (absOk hL hE (by decide) (by decide) rfl)
    (by rw [hc4.slot, fMsg, hc4.pMsg]) hln (ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide))
    (by have := L.len.isLt; omega) wm
    (by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xMsg (e := 200) (k := 640) (by omega)).symm
    (by have := hL.stk_r hL.kMsg (d := 0) (n := 32) (by omega); simpa only [BitVec.add_zero] using this))
    fun t5 ⟨hc5, hf5, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil])
  rw [hc4.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at hR5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (kpad_ok hL hE hc5 (by
      have := hL.hE
      simp only [padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, hE]
      omega) (ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)))
    fun t6 ⟨hc6, hf6, hS6⟩ => ?_)
  have hS6 := hS6 _ hR5 (by simp only [List.length_append, Proof.MlKem.bytesAt_length, List.length_cons, List.length_nil]; omega)
  refine WP.mono (ksqz_ok hL hE hc6) fun t7 ⟨hc7, hf7, hm7⟩ => ⟨hc7, ?_, ?_⟩
  · have fx : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, r = ⟨L.B, 32⟩ ∨ Within r L.XS) → Frame [L.XS, ⟨L.B, 32⟩] m m' := frameX
    have a1 := fx hf1 (by simp [w_st])
    have a2 := fx hf2 (by simp [w_st, w_ks])
    have a3 := fx hf3 (by simp [w_st, w_ks])
    have a4 := fx hf4 (by simp [w_st, w_ks])
    have a5 := fx hf5 (by simp [w_st, w_ks])
    have a6 := fx hf6 (by simp [w_st, w_ks])
    have a7 := fx hf7 (by simp [w_st, w_ks, w_mu])
    exact a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))
  · rw [hm7, hS6, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

/-! ## `tr = H(pk, 64)` -/

theorem trHash_ok (hL : L.Ok) (hE : oE p = L.E) (hk : L.keyLen = p.pkLen) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (trHash p) t fun t' => Ctx L g mx m₀ t' ∧ Frame [L.XS, ⟨L.B, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt m₀ L.key L.keyLen) 64 := by
  have hkl := hL.hKey.2
  refine WP.seq (WP.mono (zeroSt_ok hL hE hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have hR1 : Repr t1.mem L.ST 136 [] := Proof.MlKem.repr_nil hz
  have wk : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.key, L.keyLen⟩ R :=
    ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩
  refine WP.seq (WP.mono (kabs_ok hL hE hc1 (absOk hL hE (by decide) (by simp [Arg.ok]; omega) rfl)
    (by rw [hc1.slot, fKey, hc1.pKey]) (by rw [hk]; rfl) rfl (by decide) (by omega) wk
    (by have := hL.x_r hL.xKey (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm)
    (hL.x_r hL.xKey (e := 200) (k := 640) (by omega)).symm
    (by have := hL.stk_r hL.kKey (d := 0) (n := 32) (by omega); simpa only [BitVec.add_zero] using this))
    fun t2 ⟨hc2, hf2, hR2, _⟩ => ?_)
  have hR2 := hR2 [] hR1 rfl
  rw [List.nil_append, hc1.bytesAt_eq hL.xKey hL.kKey (by have := hL.nKey; omega)] at hR2
  refine WP.seq (WP.mono (kpad_ok hL hE hc2 (q := p.pkLen % 136) (by
      have := hL.hE
      simp only [padArgs, Impl.MlDsa.X86_64.Message.aSt, Impl.MlDsa.X86_64.Message.aKs, List.all_cons,
        List.all_nil, Arg.ok, fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, hE]
      omega) rfl (Nat.mod_lt _ (by decide)))
    fun t3 ⟨hc3, hf3, hS3⟩ => ?_)
  have hS3 := hS3 _ hR2 (by rw [Proof.MlKem.bytesAt_length, hk])
  refine WP.mono (ksqz_ok hL hE hc3) fun t4 ⟨hc4, hf4, hm4⟩ => ⟨hc4, ?_, ?_⟩
  · have a1 := frameX (L := L) hf1 (by simp [w_st])
    have a2 := frameX (L := L) hf2 (by simp [w_st, w_ks])
    have a3 := frameX (L := L) hf3 (by simp [w_st, w_ks])
    have a4 := frameX (L := L) hf4 (by simp [w_st, w_ks, w_mu])
    exact a1.trans (a2.trans (a3.trans a4))
  · rw [hm4, hS3, Spec.MlDsa.H, Proof.MlKem.shake256_eq]

end

end VG.Proof.MlDsa.X86_64.Message

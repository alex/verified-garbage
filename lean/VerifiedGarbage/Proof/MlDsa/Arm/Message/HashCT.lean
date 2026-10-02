import VerifiedGarbage.Proof.MlDsa.Arm.Message.Rel

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: two runs of the hashing

Untrusted: everything here is checked by Lean. In two runs with the same
layout (`Two`), zeroing the state and each call of a sponge function leak
the same: their addresses and arguments are functions of the layout alone,
and ML-KEM's lemmas on two runs of the sponge functions' calls need just that
(`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`); so do `muHash` and `trHash`.
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ct pad_ct squeeze_ct regA)
open VG.Spec.MlDsa (Params)

section
variable {I : Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zeroSt_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block zeroSt) (.block [])).isSome = true := by
  rfl

theorem zeroSt_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) (.block zeroSt) fun _ _ => True :=
  taintRel [.r7] (fun _ _ h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.r7.1) zeroSt_taint

/-! ## The sponge functions -/

theorem absA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) {src len pos : Arg} (hm : Moved (absArgs src len pos) t t1) {dp : BitVec 32} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 32 n) (hq : pos.val t = BitVec.ofNat 32 q)
    (hql : q < 136) (hnl : n < 2 ^ 32) (hfit : dp.toNat + n ≤ 2 ^ 32)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr dp, n⟩ R)
    (dS : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨State.addr dp, n⟩) :
    AbsorbArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) dp 136 q n := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.r2, pos) (by simp)
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e3 := hm.1 (.r3, src) (by simp)
  have e4 := hm.1 (.r12, len) (by simp)
  have e5 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, x0'] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have bs := below_stk hs1
  have hks := ks_eq hL
  have hcw : Covers [regA L.X32 200, regA (L.X32 + BitVec.ofNat 32 200) 640] t1.wr := by
    simp only [regA, hks, hm.2.wr, hc.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_xw0 hL
    · exact hL.covX (e := 200) (by omega)
  exact ⟨e0, e1, e2, e3, e4, e5, by decide, hql, hnl, by rw [hs1]; have := hL.nSP; omega,
    by have := hL.x32_lt; omega, hfit, by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by simp only [regA, hks]; exact st_ks, by simp only [regA]; exact dS,
    by simp only [regA, hks]; exact dK,
    by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
    by simp only [regA]; exact kD.sub_left bs, hcw,
    by simp only [regA, hm.2.rd, hm.2.wr, hc.rd, hc.wr]
       exact covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hin⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : argsOk (absArgs src len pos) = true) (dp : Lay → BitVec 32) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g m (t : State), L.Ok → Ctx L g m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 32 (n L) ∧ pos.val t = BitVec.ofNat 32 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 32 ∧ (dp L).toNat + n L ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (dp L), n L⟩ R) ∧
      Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (dp L), n L⟩) :
    RelCT isa (Two I Φ) (kabs src len pos) fun _ _ => True := by
  refine RelCT.seq (setArgs_two hok) (absorb_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, φ₁, φ₂⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, dp L, 136, q L, n L, ?_, ?_⟩)
  · obtain ⟨h1, h2, h3⟩ := hv L g₁ m₁ a hL c₁ φ₁
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hs L hL
    exact absA_of hL c₁ f₁ h1 h2 h3 s1 s2 s3 s4 s5 s6 s7
  · obtain ⟨h1, h2, h3⟩ := hv L g₂ m₂ b hL c₂ φ₂
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hs L hL
    exact absA_of hL c₂ f₂ h1 h2 h3 s1 s2 s3 s4 s5 s6 s7

theorem padA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) {pos : Arg} (hm : Moved (padArgs pos) t t1) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) :
    PadArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) 136 q (BitVec.ofNat 32 0x1f) := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.r2, pos) (by simp)
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e3 := hm.1 (.r3, .imm 0x1f) (by simp)
  have e4 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, x0'] at e0 e1 e3 e4
  rw [hq] at e2
  have bs := below_stk hs1
  have hks := ks_eq hL
  exact ⟨e0, e1, e2, e3, e4, by decide, hql, by rw [hs1]; have := hL.nSP; omega,
    by have := hL.x32_lt; omega, by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by simp only [regA, hks]; exact st_ks,
    by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
    by simp only [regA, hks, hm.2.wr, hc.wr]
       exact covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl
         · exact cov_xw0 hL
         · exact hL.covX (e := 200) (by omega)⟩

theorem kpad_tr {Φ : Lay → Mem → State → Prop} {pos : Arg}
    (hok : argsOk (padArgs pos) = true) (q : Lay → Nat)
    (hv : ∀ (L : Lay) g m (t : State), L.Ok → Ctx L g m t → Φ L m t → pos.val t = BitVec.ofNat 32 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136) :
    RelCT isa (Two I Φ) (kpad pos) fun _ _ => True :=
  RelCT.seq (setArgs_two hok) (pad_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, φ₁, φ₂⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, 136, q L,
      BitVec.ofNat 32 0x1f, padA_of hL c₁ f₁ (hv L g₁ m₁ a hL c₁ φ₁) (hs L hL),
      padA_of hL c₂ f₂ (hv L g₂ m₂ b hL c₂ φ₂) (hs L hL)⟩)

theorem sqzA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) (hm : Moved sqzArgs t t1) :
    SqueezeArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) (L.X32 + BitVec.ofNat 32 840) 136 0 64 := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e2 := hm.1 (.r2, .imm 0) (by simp)
  have e3 := hm.1 (.r3, .off oMU) (by simp)
  have e4 := hm.1 (.r12, .imm 64) (by simp)
  have e5 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, oMU, x0'] at e0 e1 e2 e3 e4 e5
  have bs := below_stk hs1
  have hks := ks_eq hL
  have hmu := mu_eq hL
  exact ⟨e0, e1, e2, e3, e4, e5, by decide, by decide, by decide, by rw [hs1]; have := hL.nSP; omega,
    by have := hL.x32_lt; omega, by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
    by simp only [regA, hmu]; exact st_mu, by simp only [regA, hks]; exact st_ks,
    by simp only [regA, hks, hmu]; exact mu_ks,
    by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hmu]; exact (k_mu hL).sub_left bs,
    by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
    by simp only [regA, hks, hmu, hm.2.wr, hc.wr]
       exact covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl
         · exact cov_xw0 hL
         · exact hL.covX (e := 840) (by omega)
         · exact hL.covX (e := 200) (by omega)⟩

theorem ksqz_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) ksqz fun _ _ => True :=
  RelCT.seq (setArgs_two (by decide)) (squeeze_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, _, _⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, L.X32 + BitVec.ofNat 32 840,
      136, 0, 64, sqzA_of hL c₁ f₁, sqzA_of hL c₂ f₂⟩)

/-! ## `μ` and `tr` -/

/-- The position after the context string. -/
abbrev qCtx (L : Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : Lay) : Nat := (qCtx L + L.len.toNat) % 136

theorem muHash_tr {Φ : Lay → Mem → State → Prop} {tr : Arg}
    (hok : tr.ok = true) (hret : tr.isRet = false) (trp : Lay → BitVec 32)
    (htr : ∀ (L : Lay) g m (t : State), Ctx L g m t → tr.val t = trp L)
    (hs : ∀ L : Lay, L.Ok → (trp L).toNat + 64 ≤ 2 ^ 32 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (trp L), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (trp L), 64⟩) :
    RelCT isa (Two I Φ) (muHash tr) fun _ _ => True := by
  -- The relation keeps only the position in `r0`.
  let Ψ : (Lay → Nat) → Lay → Mem → State → Prop := fun q L _ t => (t.gpr .r0).toNat = q L
  have z := two_wp (I := I) (Φ := Φ) (Ψ := fun _ _ _ => True) zeroSt_tr
    fun L g m₀ t hL hc _ => WP.mono (zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have a1 := two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (kabs_tr (Φ := fun _ _ _ => True) (absOk hok rfl rfl hret rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g m t _ hc _ => ⟨htr L g m t hc, rfl, rfl⟩)
      fun L hL => ⟨by decide, by decide, (hs L hL).1, (hs L hL).2.1, (hs L hL).2.2.1, (hs L hL).2.2.2.1,
        (hs L hL).2.2.2.2⟩)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e⟩ := hs L hL
      exact WP.mono (kabs_ok hL hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (absOk hok rfl rfl hret rfl) (htr L g m₀ t hc) rfl rfl (by decide)
        (by decide) a b c d e) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have hdr : ∀ L : Lay, L.Ok → 64 < 136 ∧ 2 < 2 ^ 32 ∧ (L.X32 + BitVec.ofNat 32 944).toNat + 2 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ R) ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ := fun L hL => by
    rw [hL.xo (by decide)]
    exact ⟨by decide, by decide, by rw [x32_toNat hL (by decide)]; have := hL.x32_lt; omega, cov_x hL (by omega),
      by have := Offset.disjoint L.X (d := 944) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
         simpa only [x0] using this,
      Offset.disjoint L.X (d := 944) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega),
      hL.stk_x (by omega)⟩
  have a2 := two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (kabs_tr (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.X32 + BitVec.ofNat 32 944) (fun _ => 2) (fun _ => 64)
      (fun L g m t _ hc _ => ⟨by rw [hc.off]; rfl, rfl, rfl⟩) hdr)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := hdr L hL
      exact WP.mono (kabs_ok hL hc (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.off]; rfl) rfl rfl a b c d e f k)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have ctxS : ∀ L : Lay, L.Ok → 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 32 ∧ L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.ctx, L.ctxLen.toNat⟩ R) ∧
      Region.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ := fun L hL =>
    ⟨by decide, L.ctxLen.isLt, hL.nCtx, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm, hL.kCtx⟩
  have a3 := two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ qCtx)
    (kabs_tr (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.ctx) (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g m t hL hc _ => ⟨by rw [hc.slotV hL (f := fCtx) (j := 3) rfl (by omega)]; rfl,
        by rw [hc.slotV hL (f := fCtxLen) (j := 4) rfl (by omega), ofNat_toNat32]; rfl, rfl⟩) ctxS)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := ctxS L hL
      exact WP.mono (kabs_ok hL hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV hL (f := fCtx) (j := 3) rfl (by omega)]; rfl)
        (by rw [hc.slotV hL (f := fCtxLen) (j := 4) rfl (by omega), ofNat_toNat32]; rfl) rfl a b c d e f k)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have msgS : ∀ L : Lay, L.Ok → qCtx L < 136 ∧ L.len.toNat < 2 ^ 32 ∧ L.msg.toNat + L.len.toNat ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.msg, L.len.toNat⟩ R) ∧
      Region.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ := fun L hL =>
    ⟨Nat.mod_lt _ (by decide), L.len.isLt, hL.nMsg, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm, hL.kMsg⟩
  have a4 := two_wp (I := I) (Φ := Ψ qCtx) (Ψ := Ψ qMsg)
    (kabs_tr (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.msg) (fun L => L.len.toNat) qCtx
      (fun L g m t hL hc hφ => ⟨by rw [hc.slotV hL (f := fMsg) (j := 1) rfl (by omega)]; rfl,
        by rw [hc.slotV hL (f := fLen) (j := 2) rfl (by omega), ofNat_toNat32]; rfl, ofNat_toNat_eq32 hφ⟩) msgS)
    fun L g m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := msgS L hL
      exact WP.mono (kabs_ok hL hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV hL (f := fMsg) (j := 1) rfl (by omega)]; rfl)
        (by rw [hc.slotV hL (f := fLen) (j := 2) rfl (by omega), ofNat_toNat32]; rfl) (ofNat_toNat_eq32 hφ)
        a b c d e f k) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have pd := kpad_tr (I := I) (Φ := Ψ qMsg) (pos := .ret) (padOk rfl) qMsg
    (fun L g m t _ _ hφ => ofNat_toNat_eq32 hφ) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := Ψ qMsg) (Ψ := fun _ _ _ => True) pd
    fun L g m₀ t hL hc hφ => WP.mono (kpad_ok hL hc (pos := .ret) (padOk rfl) (ofNat_toNat_eq32 hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq ksqz_tr)))))

theorem trHash_tr {p : Params} (hk : p.pkLen < 2 ^ 16)
    {Φ : Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → L.keyLen = p.pkLen) :
    RelCT isa (Two I Φ) (trHash p) fun _ _ => True := by
  have keySide : ∀ L : Lay, L.Ok → 0 < 136 ∧ L.keyLen < 2 ^ 32 ∧ L.key.toNat + L.keyLen ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.key, L.keyLen⟩ R) ∧
      Region.Disjoint ⟨State.addr L.key, L.keyLen⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.key, L.keyLen⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.key, L.keyLen⟩ := fun L hL =>
    ⟨by decide, by have := hL.hKey.2; omega, hL.nKey, ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by decide)).symm, hL.kKey⟩
  have z := two_wp (I := I) (Φ := Φ) (Ψ := fun L _ _ => L.keyLen = p.pkLen) zeroSt_tr
    fun L g m₀ t hL hc hφ => WP.mono (zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := two_wp (I := I) (Φ := fun L _ _ => L.keyLen = p.pkLen) (Ψ := fun _ _ _ => True)
    (kabs_tr (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
      (absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl) (fun L => L.key) (fun L => L.keyLen)
      (fun _ => 0) (fun L g m t hL hc hφ => ⟨by rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)]; rfl,
        by rw [hφ]; rfl, rfl⟩) keySide)
    fun L g m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := keySide L hL
      exact WP.mono (kabs_ok hL hc (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
        (n := L.keyLen) (q := 0) (absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl)
        (by rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)]; rfl) (by rw [hφ]; rfl) rfl a b c d e f k)
        fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have pd := kpad_tr (I := I) (Φ := fun _ _ _ => True) (pos := .imm (p.pkLen % 136))
    (padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) (fun _ => p.pkLen % 136)
    (fun _ _ _ _ _ _ _ => rfl) fun _ _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) pd
    fun L g m₀ t hL hc _ => WP.mono (kpad_ok hL hc (pos := .imm (p.pkLen % 136))
      (padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) rfl (Nat.mod_lt _ (by decide)))
      fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (pd'.seq ksqz_tr))

end

end VG.Proof.MlDsa.Arm.Message

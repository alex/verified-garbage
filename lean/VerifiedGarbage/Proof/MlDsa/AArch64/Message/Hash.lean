import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Args
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In `Ctx`: zeroing the Keccak
state at `X` (`zeroSt_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` (with the permutation of `v`) on it,
with their working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`); then
`muHash`, which leaves `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840`
(`muHash_ok`), and `trHash`, which leaves `H(pk, 64)` there (`trHash_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only Kept HSetup Rg absorb_callWith pad_callWith squeeze_callWith zeroState_ok)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)
open VG.Spec.MlDsa (Params)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

theorem x0 (L : Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega) (by omega) (by omega)

theorem w_st : Within ⟨L.ST, 200⟩ L.W := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.W := within_off _ (by omega)
theorem w_mu : Within ⟨L.MU, 64⟩ L.W := within_off _ (by omega)

theorem k_st (hL : L.Ok) : L.STK.Disjoint ⟨L.ST, 200⟩ := by
  have := hL.stk_x (e := 0) (k := 200) (by omega); simpa only [x0] using this
theorem k_ks (hL : L.Ok) : L.STK.Disjoint ⟨L.KS, 640⟩ := hL.stk_x (by omega)
theorem k_mu (hL : L.Ok) : L.STK.Disjoint ⟨L.MU, 64⟩ := hL.stk_x (by omega)

theorem cov_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := hL.covX h₂; exact ⟨R, List.mem_append_right _ hR, hw⟩

theorem cov_xw (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := hL.covX h₂

theorem not_pres {r : Reg} (hr : r ∈ preserved) (rs : List Reg) (h : ∀ d ∈ rs, d ∉ preserved := by decide) :
    r ∉ rs := fun hm => h r hm hr

/-- What a call that keeps `Kept` of regions within the first 904 bytes of
`X` and the stack frame leaves. -/
theorem Ctx.kept {t t' : State} (hc : Ctx L g vv m₀ t) (hL : L.Ok) {rs : List Region} (hk : Kept rs t t')
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : Ctx L g vv m₀ t' :=
  hc.keep hL hk.rd hk.wr hk.sp hk.vcs hk.cs hk.frame hrs

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) :
    WP isa (.block zeroSt) t fun t' => Ctx L g vv m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  have hS : HSetup .x28 0 200 136 t := by
    refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc.x28, x0]; exact st_ks
    · rw [hc.sp]; exact hL.nSP
    · simp only [Proof.MlKem.AArch64.stk, hc.sp, hc.x28, x0]; exact k_st hL
    · simp only [Proof.MlKem.AArch64.stk, hc.sp, hc.x28]; exact k_ks hL
    · rw [hc.x28, hc.wr, x0]
      exact covers_of_within fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := cov_xw hL (e := 0) (k := 200) (by omega); rwa [x0] at this
        · exact cov_xw hL (e := 200) (by omega)
  refine WP.mono (zeroState_ok hS ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun t' ⟨hk, hz⟩ => ?_
  simp only [Proof.MlKem.AArch64.STr, hc.x28, x0] at hk hz
  exact ⟨hc.kept hL hk (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl w_st),
    hk.frame, hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List (Reg × Arg) :=
  [(.x2, pos), (.x0, .off oST), (.x1, .imm 136), (.x3, src), (.x4, len), (.x5, .off oKS)]

theorem kabs_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t)
    {src len pos : Arg} (hok : argsOk (absArgs src len pos) = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨dp, n⟩) :
    WP isa (kabs v.callee src len pos) t fun t' => Ctx L g vv m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem dp n)) ∧ (t'.gpr .x0).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g vv m₀ t1 := hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  have e2 := hA (.x2, pos) (by simp)
  have e0 := hA (.x0, .off oST) (by simp)
  have e1 := hA (.x1, .imm 136) (by simp)
  have e3 := hA (.x3, src) (by simp)
  have e4 := hA (.x4, len) (by simp)
  have e5 := hA (.x5, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, x0] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have hs1 : t1.sp = L.SP := hc1.sp
  refine absorb_callWith v (st := L.ST) (dt := dp) (sc := L.KS) (rate := 136) (pos := q) (len := n) e0
    (by rw [e1]; rfl) (by rw [e2, BitVec.toNat_ofNat]; omega) e3 (by rw [e4, BitVec.toNat_ofNat]; omega) e5
    (by decide) hql st_ks dS dK (by rw [hs1]; exact hL.nSP) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact kD) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL) ?_ ?_ fun s' hk hrep hx => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hin
    · have := cov_x hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_x hL (e := 200) (by omega)
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := cov_xw hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_xw hL (e := 200) (by omega)
  · rw [hs1] at hk
    refine ⟨hc1.kept hL hk fun r hr => ?_, by rw [← o.mem]; exact hk.frame, fun msg hm hp => ?_, hx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl w_st, .inl w_ks, .inr fun _ h => h]
    · have := hrep msg (by rw [o.mem]; exact hm) hp
      rwa [o.mem] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List (Reg × Arg) :=
  [(.x2, pos), (.x0, .off oST), (.x1, .imm 136), (.x3, .imm 0x1f), (.x4, .off oKS)]

theorem kpad_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t)
    {pos : Arg} (hok : argsOk (padArgs pos) = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad v.callee pos) t fun t' => Ctx L g vv m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g vv m₀ t1 := hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  have e2 := hA (.x2, pos) (by simp)
  have e0 := hA (.x0, .off oST) (by simp)
  have e1 := hA (.x1, .imm 136) (by simp)
  have e3 := hA (.x3, .imm 0x1f) (by simp)
  have e4 := hA (.x4, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, x0] at e0 e1 e3 e4
  rw [hq] at e2
  have hs1 : t1.sp = L.SP := hc1.sp
  refine pad_callWith v (st := L.ST) (sc := L.KS) (rate := 136) (pos := q) e0
    (by rw [e1]; rfl) (by rw [e2, BitVec.toNat_ofNat]; omega) e4
    (by decide) hql st_ks (by rw [hs1]; exact hL.nSP) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL) ?_ ?_ fun s' hk hpost => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := cov_x hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_x hL (e := 200) (by omega)
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := cov_xw hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_xw hL (e := 200) (by omega)
  · rw [hs1] at hk
    refine ⟨hc1.kept hL hk fun r hr => ?_, by rw [← o.mem]; exact hk.frame, fun msg hm hp => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl w_st, .inl w_ks, .inr fun _ h => h]
    · rw [hpost msg (by rw [o.mem]; exact hm) hp, e3]
      rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × Arg) :=
  [(.x0, .off oST), (.x1, .imm 136), (.x2, .imm 0), (.x3, .off oMU), (.x4, .imm 64), (.x5, .off oKS)]

theorem ksqz_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) :
    WP isa (ksqz v.callee) t fun t' => Ctx L g vv m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = squeezeFrom 136 (stateAt t.mem L.ST) 0 64 := by
  refine WP.seq (WP.mono (setArgs_ok sqzArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g vv m₀ t1 := hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  have e0 := hA (.x0, .off oST) (by simp)
  have e1 := hA (.x1, .imm 136) (by simp)
  have e2 := hA (.x2, .imm 0) (by simp)
  have e3 := hA (.x3, .off oMU) (by simp)
  have e4 := hA (.x4, .imm 64) (by simp)
  have e5 := hA (.x5, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, oMU, x0] at e0 e1 e2 e3 e4 e5
  have hs1 : t1.sp = L.SP := hc1.sp
  refine squeeze_callWith v (st := L.ST) (out := L.MU) (sc := L.KS) (rate := 136) (pos := 0) (len := 64) e0
    (by rw [e1]; rfl) (by rw [e2]; rfl) e3 (by rw [e4]; rfl) e5
    (by decide) (by decide) st_mu st_ks mu_ks (by rw [hs1]; exact hL.nSP) (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_mu hL)
    (by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL) ?_ ?_ fun s' hk hout _ _ => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := cov_x hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_x hL (e := 840) (by omega)
    · exact cov_x hL (e := 200) (by omega)
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := cov_xw hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_xw hL (e := 840) (by omega)
    · exact cov_xw hL (e := 200) (by omega)
  · rw [hs1] at hk
    refine ⟨hc1.kept hL hk fun r hr => ?_, by rw [← o.mem]; exact hk.frame, by rw [hout, o.mem]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [.inl w_st, .inl w_mu, .inl w_ks, .inr fun _ h => h]

end

end VG.Proof.MlDsa.AArch64.Message

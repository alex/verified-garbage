import VerifiedGarbage.Proof.MlDsa.Arm.Message.Args
import VerifiedGarbage.Proof.MlKem.Arm.Sample

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In `Ctx`: zeroing the Keccak
state at `X` (`zeroSt_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` in their frames on it, with their
working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from ML-KEM's
call lemmas, `Proof/MlKem/Arm/Keccak.lean`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ok pad_ok squeeze_ok regA below Kept)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem x0 (L : Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _

theorem x0' (L : Lay) : L.X32 + BitVec.ofNat 32 0 = L.X32 := BitVec.add_zero _

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

/-- The 8 bytes a call's frame pushes lie in `STK`. -/
theorem below_stk {t : State} (hsp : t.sp = L.SP) : Region.Sub (below t 8) L.STK := by
  simp only [below, hsp]; exact Offset.sub_below _ (by omega) (by omega)

theorem cov_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := hL.covX h₂; exact ⟨R, List.mem_append_right _ hR, hw⟩

theorem cov_x0 (hL : L.Ok) : ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X, 200⟩ R := by
  have := cov_x hL (e := 0) (k := 200) (by omega); rwa [x0] at this

theorem cov_xw0 (hL : L.Ok) : ∃ R ∈ L.wr, Within ⟨L.X, 200⟩ R := by
  have := hL.covX (e := 0) (k := 200) (by omega); rwa [x0] at this

theorem not_pres {r : Reg} (hr : r ∈ preserved) (hl : r ≠ .lr) (rs : List Reg)
    (h : ∀ d ∈ rs, d ∉ preserved ∨ d = .lr := by decide) : r ∉ rs := fun hm => by
  rcases h r hm with h | h
  · exact h hr
  · exact hl h

/-- The address of the sponge functions' working space. -/
theorem ks_eq (hL : L.Ok) : State.addr (L.X32 + BitVec.ofNat 32 200) = L.KS := hL.xo (by decide)
theorem mu_eq (hL : L.Ok) : State.addr (L.X32 + BitVec.ofNat 32 840) = L.MU := hL.xo (by decide)

theorem x32_toNat (hL : L.Ok) {o : Nat} (ho : o < 1024) : (L.X32 + BitVec.ofNat 32 o).toNat = L.X32.toNat + o := by
  have := hL.x32_lt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- What a call that keeps `Kept` of regions within the first 904 bytes of
`X` and its frame leaves. -/
theorem Ctx.kept {t t' : State} (hc : Ctx L g m₀ t) (hL : L.Ok) {rs : List Region} (hk : Kept rs t t')
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : Ctx L g m₀ t' :=
  hc.keep hL hk.rd hk.wr hk.sp hk.cs hk.frame hrs

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block zeroSt) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  rw [zeroSt, Impl.MlKem.Arm.zeroState, ← List.singleton_append, WP.block_append_iff]
  refine wp_movImm (d := .r12) (v := 0) (by decide) fun t1 o1 e1 => wp_nil ?_
  have e7 : t1.gpr .r7 = L.X32 := by rw [o1.get .r7, hc.r7]
  refine WP.mono (Proof.MlKem.Arm.Sample.zeroWords_ok .r7 (s₁ := t1) e1 (by rw [e7]; have := hL.x32_lt; omega)
    fun k hk => by rw [e7, o1.wr, hc.wr]; exact hL.inW (by omega)) fun t2 h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7] at hf hz
  have hc1 : Ctx L g m₀ t1 := hc.regs o1.rd o1.wr o1.sp o1.mem fun r hr hl => o1.gpr r (not_pres hr hl _)
  rw [o1.mem] at hf
  refine ⟨hc1.keep hL h₂.rd h₂.wr h₂.sp (fun r _ _ => by rw [h₂.gpr]) (by rwa [o1.mem])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl w_st), hf,
    Proof.MlKem.Arm.Sample.stateAt_zero hz⟩

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List (Reg × Arg) :=
  [(.r2, pos), (.r0, .off oST), (.r1, .imm 136), (.r3, src), (.r12, len), (.lr, .off oKS)]

theorem kabs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    {src len pos : Arg} (hok : argsOk (absArgs src len pos) = true)
    {dp : BitVec 32} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 32 n)
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) (hnl : n < 2 ^ 32) (hfit : dp.toNat + n ≤ 2 ^ 32)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr dp, n⟩ R)
    (dS : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨State.addr dp, n⟩) :
    WP isa (kabs src len pos) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem (State.addr dp) n)) ∧ (t'.gpr .r0).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  have e2 := hA (.r2, pos) (by simp)
  have e0 := hA (.r0, .off oST) (by simp)
  have e1 := hA (.r1, .imm 136) (by simp)
  have e3 := hA (.r3, src) (by simp)
  have e4 := hA (.r12, len) (by simp)
  have e5 := hA (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, x0'] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have hs1 : t1.sp = L.SP := hc1.sp
  have bs := below_stk hs1
  have hks := ks_eq hL
  refine absorb_ok (st := L.X32) (scr := L.X32 + BitVec.ofNat 32 200) (data := dp) (rate := 136) (pos := q)
    (len := n) ⟨e0, e1, e2, e3, e4, e5, by decide, hql, hnl, by rw [hs1]; have := hL.nSP; omega,
      by have := hL.x32_lt; omega, hfit, by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by simp only [regA, hks]; exact st_ks, by simp only [regA]; exact dS,
      by simp only [regA, hks]; exact dK,
      by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
      by simp only [regA]; exact kD.sub_left bs, ?_, ?_⟩ fun s' hk hrep hx => ?_
  · simp only [regA, hks, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_xw0 hL
    · exact hL.covX (e := 200) (by omega)
  · simp only [regA, hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hin
  · simp only [regA, hks] at hk hrep
    refine ⟨hc1.kept hL hk fun r hr => ?_, ?_, fun msg hm hp => ?_, hx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl w_st, .inl w_ks, .inr bs]
    · rw [← o.mem]
      exact hk.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, by simp, bs⟩
    · have := hrep msg (by rw [o.mem]; exact hm) hp
      rwa [o.mem] at this

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List (Reg × Arg) :=
  [(.r2, pos), (.r0, .off oST), (.r1, .imm 136), (.r3, .imm 0x1f), (.lr, .off oKS)]

theorem kpad_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    {pos : Arg} (hok : argsOk (padArgs pos) = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) :
    WP isa (kpad pos) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  have e2 := hA (.r2, pos) (by simp)
  have e0 := hA (.r0, .off oST) (by simp)
  have e1 := hA (.r1, .imm 136) (by simp)
  have e3 := hA (.r3, .imm 0x1f) (by simp)
  have e4 := hA (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, x0'] at e0 e1 e3 e4
  rw [hq] at e2
  have hs1 : t1.sp = L.SP := hc1.sp
  have bs := below_stk hs1
  have hks := ks_eq hL
  refine pad_ok (st := L.X32) (scr := L.X32 + BitVec.ofNat 32 200) (rate := 136) (pos := q)
    ⟨e0, e1, e2, e3, e4, by decide, hql, by rw [hs1]; have := hL.nSP; omega,
      by have := hL.x32_lt; omega, by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by simp only [regA, hks]; exact st_ks,
      by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
      ?_⟩ fun s' hk hpost => ?_
  · simp only [regA, hks, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_xw0 hL
    · exact hL.covX (e := 200) (by omega)
  · simp only [regA, hks] at hk hpost
    refine ⟨hc1.kept hL hk fun r hr => ?_, ?_, fun msg hm hp => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [.inl w_st, .inl w_ks, .inr bs]
    · rw [← o.mem]
      exact hk.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, by simp, bs⟩
    · rw [hpost msg (by rw [o.mem]; exact hm) hp]
      rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × Arg) :=
  [(.r0, .off oST), (.r1, .imm 136), (.r2, .imm 0), (.r3, .off oMU), (.r12, .imm 64), (.lr, .off oKS)]

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa ksqz t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = squeezeFrom 136 (stateAt t.mem L.ST) 0 64 := by
  refine WP.seq (WP.mono (setArgs_ok sqzArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  have e0 := hA (.r0, .off oST) (by simp)
  have e1 := hA (.r1, .imm 136) (by simp)
  have e2 := hA (.r2, .imm 0) (by simp)
  have e3 := hA (.r3, .off oMU) (by simp)
  have e4 := hA (.r12, .imm 64) (by simp)
  have e5 := hA (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, oMU, x0'] at e0 e1 e2 e3 e4 e5
  have hs1 : t1.sp = L.SP := hc1.sp
  have bs := below_stk hs1
  have hks := ks_eq hL
  have hmu := mu_eq hL
  refine squeeze_ok (st := L.X32) (scr := L.X32 + BitVec.ofNat 32 200) (out := L.X32 + BitVec.ofNat 32 840)
    (rate := 136) (pos := 0) (len := 64)
    ⟨e0, e1, e2, e3, e4, e5, by decide, by decide, by decide, by rw [hs1]; have := hL.nSP; omega,
      by have := hL.x32_lt; omega, by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by rw [x32_toNat hL (by omega)]; have := hL.x32_lt; omega,
      by simp only [regA, hmu]; exact st_mu, by simp only [regA, hks]; exact st_ks,
      by simp only [regA, hks, hmu]; exact mu_ks,
      by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hmu]; exact (k_mu hL).sub_left bs,
      by simp only [regA, hks]; exact (k_ks hL).sub_left bs, ?_⟩ fun s' hk hout _ _ => ?_
  · simp only [regA, hks, hmu, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_xw0 hL
    · exact hL.covX (e := 840) (by omega)
    · exact hL.covX (e := 200) (by omega)
  · simp only [regA, hks, hmu] at hk hout
    refine ⟨hc1.kept hL hk fun r hr => ?_, ?_, by rw [hout, o.mem]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [.inl w_st, .inl w_mu, .inl w_ks, .inr bs]
    · rw [← o.mem]
      exact hk.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, bs⟩

end

end VG.Proof.MlDsa.Arm.Message

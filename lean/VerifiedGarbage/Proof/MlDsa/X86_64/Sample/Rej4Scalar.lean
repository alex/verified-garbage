import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4`

Untrusted: everything here is checked by Lean. The baseline implementation
calls `vg_mldsa_rej_ntt_poly` on each seed, between the prologue and the
epilogue of the one for AVX2 (`Rej4Top.lean`): after the call on seed `K`,
polynomial `K` is the seed's `RejNTTPoly` if it has 256 coefficients, and
`r14` records whether the first `K + 1` do (`PC`), as in
`vg_mlkem_sample_ntt4` (`MlKem/X86_64/S4Scalar.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (rejNTT4)
open VG.Proof.MlKem.X86_64 (Keep sample4K relInv taintRel relStart Rel2 pR ret_disj24 stk_disj24'
  ce_bytesAt24 ce_gpr' WP.keep nosp_of)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' sd scr aR scrR stkR sdR pre_of pub_scr pub_aP pub_B pub_sd pub_sp
  env_rbx pro_ok I0 sub_scr sub_poly seed_bytes cov scr6144_lt sx34 sx1024 sx6144 c_sub c_disj and14_ok epi_eq
  cRd cWr in_scr')
open VG.Proof.MlDsa.X86_64.Sample (rnK nil_regs rejNTT_correct rejNTT_ct)
open VG.Proof.MlDsa.Sample (rnFold toPoly)
open VG.Proof.MlDsa.Arith (polyIs_frame)
open VG.Spec.MlKem (poly4)
open VG.Spec.MlDsa (G PolyIs)

theorem rn_nosp : NoSp Impl.MlDsa.X86_64.Sample.rejNTT := nosp_of (by decide +kernel)

theorem rn_depth : Impl.MlDsa.X86_64.Sample.rejNTT.depth = 2 := by decide +kernel

/-- Before the call on seed `K`. -/
structure PC (σ : State) (K : Nat) (s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ K)
  polys : ∀ k < K, (Lt σ k 336).length = 256 → PolyIs s.mem (poly4 (aP σ) k) (toPoly (Lt σ k 336))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
/-- `PC` after code that writes no memory and keeps its registers. -/
theorem PC.keep {K : Nat} {s s' : State} (h : PC σ K s) (hm : s'.mem = s.mem) {rs : List Reg}
    (hk : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs) : PC σ K s' :=
  ⟨h.env.keep hm hk fun r hr => hrs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hk.gpr (hrs .r14 (by simp)), h.r14], by rw [hm]; exact h.polys⟩

/-- `PC` after the call. -/
theorem PC.call {K : Nat} (hK : K < 4) {s s' : State} (h : PC σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r)
    (hf : Frame (cWr σ K ++ [stkR σ]) s.mem s'.mem) : PC σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub (c_sub (σ := σ) hK))⟩,
    by rw [hg .r14 (by simp), h.r14], fun k hk e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (c_disj hp hK (by simp only [oSave, oScalar]; omega)) (by decide)]
    exact h.env.saved i hi
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk e)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
        (by omega)
      simpa [poly4] using hd
    · exact (hp.a_scr.sub_left (sub_poly (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega))
    · exact (hp.stk_a.sub_right (sub_poly (by omega))).symm

/-- The arguments of the call on seed `K`. -/
structure ArgI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : PC σ K s
  rdi : s.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K)
  rsi : s.gpr .rsi = poly4 (aP σ) K
  rdx : s.gpr .rdx = at' σ oScalar

omit hp in
theorem argsK_ok {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) s (ArgI σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K) ∧ s'.gpr .rsi = poly4 (aP σ) K ∧ s'.gpr .rdx = at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.rbx, sx34 hK, sx1024 hK, sx6144]; exact ⟨rfl, rfl⟩) rfl)
    fun _ ⟨⟨hm₂, hdi, hsi, hdx⟩, k₂⟩ => ⟨h.keep hm₂ k₂ (by decide), hdi, hsi, hdx⟩

theorem argK_kS {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨sd σ + BitVec.ofNat 64 (34 * K), 34⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (sd σ) (d := 34 * K) (n := 34) (by omega))

theorem argK_pre {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    rnK.pre (s.callEntry.withRegions (cRd σ K) (cWr σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (pR (poly4 (aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega))
  simp only [rnK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega)),
    (hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (by simp only [oScalar]; omega)),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    scr6144_lt hp⟩

/-- After the call on seed `K`. -/
structure CallI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : PC σ K s
  rax : (s.gpr .rax).setWidth 32 = if (Lt σ K 336).length = 256 then 1 else 0
  poly : (Lt σ K 336).length = 256 → PolyIs s.mem (poly4 (aP σ) K) (toPoly (Lt σ K 336))

theorem callK_ok {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    WP isa (.call "vg_mldsa_rej_ntt_poly" Impl.MlDsa.X86_64.Sample.rejNTT) s (CallI σ K) := by
  have hcv := cov hp h.pinv.env hK
  refine WP.call rejNTT_correct rn_nosp (by rw [rn_depth]; decide) (argK_pre hp hK h) hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, hg₃, hpost⟩ => ?_
  rw [rn_depth, h.pinv.env.rsp] at hf
  have h₃ : PC σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf
  simp only [rnK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rsi, hm₃, ce_bytesAt24 s (n := 34) (by decide) (argK_kS hp hK h),
    seed_bytes hp hK h.pinv.env.frame] at hpost
  rw [hg₃ .rax (by decide)] at hpost
  simp only [← Lt_336] at hpost
  exact ⟨h₃, hpost.1, hpost.2⟩

omit hp in
theorem okN_succ' (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (okN σ K)).setWidth 32 &&&
    (if (Lt σ K 336).length = 256 then 1 else 0)) = BitVec.ofNat 64 (okN σ (K + 1)) := by
  simp only [okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  by_cases e : (Lt σ K 336).length = 256
  · rw [ite_eq_left e, show ((Lt σ K 336).length == 256) = true by simpa using e]
    cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;> rfl
  · rw [ite_eq_right e, show ((Lt σ K 336).length == 256) = false by simpa using e]
    cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;> rfl

omit hp in
theorem andK_ok {K : Nat} {s : State} (h : CallI σ K s) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s (PC σ (K + 1)) := by
  refine WP.mono (and14_ok s) fun s₄ ⟨⟨h14, hm₄⟩, k₄⟩ => ?_
  refine ⟨h.pinv.env.keep hm₄ k₄ (by decide), by rw [h14, h.pinv.r14, h.rax, okN_succ'], fun k hk e => ?_⟩
  rw [hm₄]
  by_cases ek : k = K
  · subst ek; exact h.poly e
  · exact h.pinv.polys k (by omega) e

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) : WP isa (Impl.MlDsa.X86_64.Sample.Rej4.callK K) s (PC σ (K + 1)) :=
  WP.seq (WP.mono (argsK_ok hK h) fun _ h₂ => WP.seq (WP.mono (callK_ok hp hK h₂) fun _ h₃ => andK_ok h₃))

/-- The return value, and the callee-saved registers restored. -/
theorem endS_ok {s : State} (h : PC σ 4 s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    simp only [Lt_336]
    split <;> rfl
  · rw [hm, ← Lt_336]
    rw [← Lt_336] at e
    exact h.polys k hk e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

theorem scalar_body_ok {s : State} (h : I0 σ s) :
    WP isa (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 0) (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 1)
      (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 2) (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 3) (.block epi)))))
      s fun s' =>
      r4K.post σ s' ∧ gprPreserved σ s' := by
  have p₀ : PC σ 0 s := ⟨h.env, by rw [h.r14]; rfl, fun _ h _ => absurd h (by omega)⟩
  exact WP.seq (WP.mono (callK_ok' hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (callK_ok' hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (callK_ok' hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (callK_ok' hp (by decide) p₃) fun _ p₄ => endS_ok hp p₄))))

end

theorem correct_scalar (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa rejNTT4 σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun _ h => scalar_body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

/-! ## Constant time -/

/-- The call on seed `K`. -/
theorem call_ct {K : Nat} (hK : K < 4) :
    RelCT isa (R4 fun σ s => ArgI σ K s) (.call "vg_mldsa_rej_ntt_poly" Impl.MlDsa.X86_64.Sample.rejNTT)
      (R4 fun σ s => CallI σ K s) :=
  relInv (fun σ s hp h => callK_ok (pre_of hp) hK h) (RelCT.callEx rejNTT_correct rejNTT_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, pub_sp hq]
      refine ⟨_, _, _, _, argK_pre (pre_of p₁) hK h₁, argK_pre (pre_of p₂) hK h₂, ?_,
        (cov (pre_of p₁) h₁.pinv.env hK).1, (cov (pre_of p₁) h₁.pinv.env hK).2,
        (cov (pre_of p₂) h₂.pinv.env hK).1, (cov (pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [rnK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rdx, h₂.rdx]
      rw [ce_bytesAt24 s₁ (n := 34) (by decide) (argK_kS (pre_of p₁) hK h₁),
        ce_bytesAt24 s₂ (n := 34) (by decide) (argK_kS (pre_of p₂) hK h₂),
        seed_bytes (pre_of p₁) hK h₁.pinv.env.frame, seed_bytes (pre_of p₂) hK h₂.pinv.env.frame, pub_B hq hK]
      simp only [pub_sd hq, pub_aP hq, at', pub_scr hq, hsp, and_self])

/-- The call on seed `K`, given the taint analysis of its arguments. -/
theorem callK_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R4 fun σ s => PC σ K s) (Impl.MlDsa.X86_64.Sample.Rej4.callK K) (R4 fun σ s => PC σ (K + 1) s) :=
  RelCT.seq (relInv (fun σ s _ h => argsK_ok hK h) (taintRel [.r12, .r13, .rbx]
      (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.env.r12, h₂.env.r12, pub_sd hq]
        · rw [h₁.env.r13, h₂.env.r13, pub_aP hq]
        · exact env_rbx hq h₁.env h₂.env) c))
    (RelCT.seq (call_ct hK) (relInv (fun σ s _ h => andK_ok h) (taintRel [] nil_regs (by taint_decide))))

theorem ct_scalar : ConstantTime isa r4K.pre r4K.pub rejNTT4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => PC σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (pro_ok (pre_of hp)) fun _ h => ⟨h.env, by rw [h.r14]; rfl, fun _ h _ => absurd h (by omega)⟩)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))) (fun _ _ h => h) fun _ _ h => h) ?_)
  refine RelCT.seq (callK_ct (K := 0) (by decide) (by taint_decide)) (RelCT.seq (callK_ct (K := 1) (by decide)
    (by taint_decide)) (RelCT.seq (callK_ct (K := 2) (by decide) (by taint_decide))
      (RelCT.seq (callK_ct (K := 3) (by decide) (by taint_decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Rej4

import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4CT
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
import VerifiedGarbage.Proof.MlKem.X86_64.FragCall

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4`

Untrusted: everything here is checked by Lean. The baseline implementation
calls `vg_mldsa_expand_mask_poly` on each seed, between the prologue and the
epilogue of the one for AVX2: after the call on seed `K`, polynomial `K` is
`ExpandMask`'s for the seed (`PC`), as in `vg_mldsa_rej_ntt_poly4`
(`Rej4Scalar.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emK gOf expandMask_correct expandMask_ct)
open VG.Proof.MlDsa.Arith (polyIs_frame)
open VG.Spec.MlDsa (PolyIs H toRq bitUnpack bitlen seed66)
open VG.Spec.Sha3 (bytesAt)

theorem em_nosp : NoSp Impl.MlDsa.X86_64.Sample.expandMask := nosp_of (by decide +kernel)

theorem em_depth : Impl.MlDsa.X86_64.Sample.expandMask.depth = 2 := by decide +kernel

/-- `ExpandMask`'s polynomial for seed `k`. -/
abbrev P (σ : State) (k : Nat) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (B σ k) (32 * (1 + bitlen (gOf σ - 1)))) (gOf σ - 1) (gOf σ))

/-- Before the call on seed `K`. -/
structure PC (σ : State) (K : Nat) (s : State) : Prop where
  env : Env σ s
  polys : ∀ k < K, PolyIs s.mem (poly4 (aP σ) k) (P σ k)

/-- The regions of `vg_mldsa_expand_mask_poly`'s call for seed `K`. -/
abbrev cRd (σ : State) (K : Nat) : List Region := [⟨sd σ + BitVec.ofNat 64 (66 * K), 66⟩]
abbrev cWr (σ : State) (K : Nat) : List Region := [pR (poly4 (aP σ) K), ⟨at' σ oScalar, 2048⟩]

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem c_sub {K : Nat} (hK : K < 4) : ∀ r ∈ cWr σ K ++ [stkR σ],
    (∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨aR σ, by simp, sub_poly hK⟩
  · exact ⟨scrR σ, by simp, sub_scr (by simp only [oScalar]; omega)⟩
  · exact ⟨stkR σ, by simp, fun _ h => h⟩

/-- A region the call writes is apart from `⟨at' σ a, n⟩` in the scratch space below 6144. -/
theorem c_disj {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ oScalar) :
    ∀ r ∈ cWr σ K ++ [stkR σ], Region.Disjoint ⟨at' σ a, n⟩ r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact (hp.a_scr.symm.sub_left (sub_scr (by simp only [oScalar] at h; omega))).sub_right (sub_poly hK)
  · exact Offset.disjoint _ (.inl h) (by simp only [oScalar] at h; omega) (by simp only [oScalar]; omega)
  · exact (hp.stk_scr.sub_right (sub_scr (by simp only [oScalar] at h; omega))).symm

theorem seed_bytes {K : Nat} (hK : K < 4) {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) :
    bytesAt m (sd σ + BitVec.ofNat 64 (66 * K)) 66 = B σ K := by
  rw [MlKem.bytesAt_frame hf (by simpa using ⟨hp.sd_a.sub_left (Offset.sub_base _ (by omega)),
    hp.sd_scr.sub_left (Offset.sub_base _ (by omega)), (hp.stk_sd.sub_right (Offset.sub_base _ (by omega))).symm⟩)
    (by decide)]
  rfl

theorem scr6144_lt : (at' σ oScalar).toNat + 2048 ≤ 2 ^ 64 := by
  have := hp.scr_lt
  rw [at', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show oScalar < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (by simp only [oScalar]; omega)]
  simp only [oScalar]; omega

theorem regs {s : State} (he : Env σ s) : s.rd ++ s.wr = [sdR σ, aR σ, scrR σ] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov {s : State} (he : Env σ s) {K : Nat} (hK : K < 4) :
    Covers (cRd σ K ++ cWr σ K) (s.rd ++ s.wr) ∧ Covers (cWr σ K) s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rw [regs hp he]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sdR σ, by simp, 66 * K, rfl, by simp only; omega⟩
    · exact ⟨aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩
  · rw [he.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩

/-- `PC` after the call. -/
theorem PC.call {K : Nat} (hK : K < 4) {s s' : State} (h : PC σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r)
    (hf : Frame (cWr σ K ++ [stkR σ]) s.mem s'.mem) : PC σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .r14 (by simp), h.env.r14],
      by rw [hg .rsp (by simp), h.env.rsp], by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_,
      h.env.frame.trans (hf.sub (c_sub (σ := σ) hK))⟩, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (c_disj hp hK (by simp only [oSave, oScalar]; omega)) (by decide)]
    exact h.env.saved i hi
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk)
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
  rdi : s.gpr .rdi = sd σ + BitVec.ofNat 64 (66 * K)
  rsi : s.gpr .rsi = σ.gpr .rsi
  rdx : s.gpr .rdx = poly4 (aP σ) K
  rcx : s.gpr .rcx = at' σ oScalar

omit hp in
theorem sx6144 : BitVec.signExtend 64 (BitVec.ofNat 32 oScalar) = BitVec.ofNat 64 6144 := by decide

omit hp in
theorem argsK_ok {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (66 * K))), .mov .rsi (.reg .r14),
      .mov .rdx (.reg .r13), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rcx (.reg .rbx),
      .alu .add .rcx (.imm (BitVec.ofNat 32 oScalar))]) s (ArgI σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = sd σ + BitVec.ofNat 64 (66 * K) ∧ s'.gpr .rsi = σ.gpr .rsi ∧ s'.gpr .rdx = poly4 (aP σ) K ∧
      s'.gpr .rcx = at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.r14, h.env.rbx, sx_ofNat (show 66 * K < 2 ^ 31 by omega),
      sx_ofNat (show 1024 * K < 2 ^ 31 by omega), sx6144]; rfl) (by rfl))
    fun _ ⟨⟨hm₂, hdi, hsi, hdx, hcx⟩, k₂⟩ => ⟨⟨h.env.keep hm₂ k₂ (by decide), by rw [hm₂]; exact h.polys⟩,
      hdi, hsi, hdx, hcx⟩

theorem argK_kS {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨sd σ + BitVec.ofNat 64 (66 * K), 66⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (sd σ) (d := 66 * K) (n := 66) (by omega))

theorem argK_pre {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    emK.pre (s.callEntry.withRegions (cRd σ K) (cWr σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (pR (poly4 (aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega))
  simp only [emK, gOf, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), ce_gpr' s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega)),
    (hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (by simp only [oScalar]; omega)),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    scr6144_lt hp, hp.gamma⟩

theorem callK_ok {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    WP isa (.call "vg_mldsa_expand_mask_poly" Impl.MlDsa.X86_64.Sample.expandMask) s (PC σ (K + 1)) := by
  have hcv := cov hp h.pinv.env hK
  refine WP.call expandMask_correct em_nosp (by rw [em_depth]; decide) (argK_pre hp hK h) hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, _, hpost⟩ => ?_
  rw [em_depth, h.pinv.env.rsp] at hf
  have h₃ : PC σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf
  simp only [emK, gOf, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hm₃,
    ce_bytesAt24 s (n := 66) (by decide) (argK_kS hp hK h), seed_bytes hp hK h.pinv.env.frame] at hpost
  refine ⟨h₃.env, fun k hk => ?_⟩
  by_cases e : k = K
  · subst e; exact hpost
  · exact h₃.polys k (by omega)

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) : WP isa (callK K) s (PC σ (K + 1)) :=
  WP.seq (WP.mono (argsK_ok hK h) fun _ h₂ => callK_ok hp hK h₂)

omit hp in
theorem epi_eq' : epi = [.mov .r14 (.mem (at_ .rbx 5120)), .mov .r13 (.mem (at_ .rbx 5112)),
    .mov .r12 (.mem (at_ .rbx 5104)), .mov .rbp (.mem (at_ .rbx 5096)), .mov .rbx (.mem (at_ .rbx 5088))] := rfl

/-- The postcondition, and the callee-saved registers restored. -/
theorem endS_ok {s : State} (h : PC σ 4 s) :
    WP isa (.block epi) s fun s' => em4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [epi_eq']
  refine WP.mono (WP.keep [.r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨fun K hK => by rw [hm]; exact h.polys K hK, fun r hr => ?_, ?_⟩
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

end

theorem correct_scalar (σ : State) (hs : em4K.pre σ) :
    ∃ t s', Exec isa expandMask4 σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun _ h =>
    WP.seq (WP.mono (callK_ok' hp (by decide) (⟨h, fun _ h' => absurd h' (by omega)⟩ : PC σ 0 _)) fun _ p₁ =>
      WP.seq (WP.mono (callK_ok' hp (by decide) p₁) fun _ p₂ => WP.seq (WP.mono (callK_ok' hp (by decide) p₂)
        fun _ p₃ => WP.seq (WP.mono (callK_ok' hp (by decide) p₃) fun _ p₄ => endS_ok hp p₄)))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Mask4

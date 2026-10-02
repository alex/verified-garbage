import VerifiedGarbage.Proof.AesGcm.AArch64.Init
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code around the calls by
the taint analysis, from the public arguments and the registers the
correctness proof pins (`init1_ok`, `init2_ok`); the calls by their callees'
proofs, with the arguments those proofs give.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The block before the call of `vg_aes_expand_key`. -/
theorem init1_ok {s : State} {K Ctx W : Addr} {L : Nat} (hK : s.gpr .x0 = K) (hLn : (s.gpr .x1).toNat = L)
    (hCtx : s.gpr .x2 = Ctx) (hW : s.gpr .x3 = W) (hrd : s.rd = [⟨K, L⟩])
    (hwr : s.wr = [⟨Ctx, 256⟩, ⟨W, 2560⟩]) (d_kc : (⟨K, L⟩ : Region).Disjoint ⟨Ctx, 256⟩)
    (d_ks : (⟨K, L⟩ : Region).Disjoint ⟨W, 2560⟩) (d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    WP isa (.block initSeg1) s fun s₂ => KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L ∧ s₂.gpr .x19 = W ∧
      s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧ s₂.sp = s.sp ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x3 hW pW
  have hsi : s.gpr .x1 = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x21₂, x22₂, x3₂, x0₂, x1₂, x2₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x3, mov .x21 .x2, .lsr .x .x22 .x1 2, .addImm .x .x22 .x22 6, ptr .x3 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .x3 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 L ∧
      s₂.gpr .x2 = Ctx ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, g₁, hsi, BitVec.setWidth_eq]
      exact rounds_of_len hL
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hsi]
    · simp [gpr_write, g₁, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := covers_off pW (by decide) (by decide)
  refine ⟨⟨x0₂, x1₂, x2₂, x3₂, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
      d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩, x19₂, x21₂, x22₂, by rw [sp₂, sp₁], rd₂', wr₂'⟩
  · rw [rd₂', wr₂', hrd]
    exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
      (covers_left (covers_cons (covers_prefix pC (by decide)) pS))
  · rw [wr₂']; exact covers_cons (covers_prefix pC (by decide)) pS

/-- The block before the call of `vg_aes_ctr32`. -/
theorem init2_ok {s : State} {Ctx W : Addr} {R : Nat} (h19 : s.gpr .x19 = W) (h21 : s.gpr .x21 = Ctx)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR' : R = 10 ∨ R = 12 ∨ R = 14)
    (pC : Covers [⟨Ctx, 256⟩] s.wr) (pW : Covers [⟨W, 2560⟩] s.wr) (d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩)
    (wc : Ctx.toNat + 256 ≤ 2 ^ 64) :
    WP isa (.block initSeg2) s fun s₄ =>
      CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 ∧
      s₄.gpr .x19 = W ∧ s₄.sp = s.sp := by
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  obtain ⟨s₄, run₄, x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s = some s₄ ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .x3 = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] s s₄ ∧
      s₄.sp = s.sp ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [h19, h21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, h21]
    · simp [gpr_write, h22]
    · simp [gpr_write, h19]
    · simp [gpr_write, h21]
    · simp [gpr_write]
    · simp [gpr_write, h19]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [og₄ _ (by decide), h19], sp₄⟩
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  refine ⟨x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, hR', ?_, by decide, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
  · simpa using dCW 0 240 (by decide) 96 16 (by decide)
  · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
  · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact dCW 240 16 (by decide) 512 2048 (by decide)
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide))) (covers_cons
      (covers_left (covers_off pC' (by decide) (by decide))) (covers_left (covers_off pW' (by decide) (by decide)))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_cons (covers_off pC' (by decide) (by decide))
      (covers_off pW' (by decide) (by decide)))

theorem init_ct (v : GcmImpl) : ConstantTime isa initAArch64.pre initAArch64.pub (init v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  simp only [initAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q3] at h₂
  obtain ⟨hrd₁, hwr₁, d_kc, d_ks, d_cs, wc, ws, hL⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hK : σ₁.gpr .x0 = K at *
  generalize hLn : (σ₁.gpr .x1).toNat = L at *
  generalize hCtx : σ₁.gpr .x2 = Ctx at *
  generalize hW : σ₁.gpr .x3 = W at *
  have hR' : Spec.Aes.rounds (L / 4) = 10 ∨ Spec.Aes.rounds (L / 4) = 12 ∨ Spec.Aes.rounds (L / 4) = 14 := by
    rcases hL with rfl | rfl | rfl <;> decide
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3] qsp (by agree_tac [hK, hCtx, hW, ← q0, q1, ← q2, ← q3])
      ⟨_, by taint_decide⟩)
    (init1_ok hK hLn hCtx hW hrd₁ hwr₁ d_kc d_ks d_cs hL)
    (init1_ok q0.symm (by rw [← q1, hLn]) q2.symm q3.symm hrd₂ hwr₂ d_kc d_ks d_cs hL)
    fun τ₁ τ₂ ⟨k₁, x19₁, x21₁, x22₁, sp₁, rd₁, wr₁⟩ ⟨k₂, x19₂, x21₂, x22₂, sp₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_key v.key k₁ k₂ (by rw [sp₁, sp₂, qsp])) (key_call v.key k₁) (key_call v.key k₂)
    fun τ₁' τ₂' g₁ g₂ => ?_
  have pv : ∀ {σ τ τ' : State}, σ.wr = [⟨Ctx, 256⟩, ⟨W, 2560⟩] → τ.wr = σ.wr →
      KeyPost τ K Ctx (W + BitVec.ofNat 64 512) L τ' → τ.gpr .x19 = W → τ.gpr .x21 = Ctx →
      τ.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) →
      WP isa (.block initSeg2) τ' fun s₄ => CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240)
        (W + BitVec.ofNat 64 512) (Spec.Aes.rounds (L / 4)) 1 ∧ s₄.gpr .x19 = W ∧ s₄.sp = τ'.sp :=
    fun hwr wr g h19 h21 h22 => init2_ok (by rw [g.saved .x19 (by decide) (by decide), h19])
      (by rw [g.saved .x21 (by decide) (by decide), h21]) (by rw [g.saved .x22 (by decide) (by decide), h22]) hR'
      (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp)) (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp))
      d_cs wc
  refine rel_seq (rel_taint [.x19, .x21, .x22] (by rw [g₁.sp, g₂.sp, sp₁, sp₂, qsp])
      (by agree_tac [g₁.saved .x19 (by decide) (by decide), g₂.saved .x19 (by decide) (by decide),
        g₁.saved .x21 (by decide) (by decide), g₂.saved .x21 (by decide) (by decide),
        g₁.saved .x22 (by decide) (by decide), g₂.saved .x22 (by decide) (by decide), x19₁, x19₂, x21₁, x21₂,
        x22₁, x22₂]) ⟨_, by taint_decide⟩)
    (pv hwr₁ wr₁ g₁ x19₁ x21₁ x22₁) (pv hwr₂ wr₂ g₂ x19₂ x21₂ x22₂) fun τ₁ τ₂ ⟨c₁, y₁, s₁'⟩ ⟨c₂, y₂, s₂'⟩ => ?_
  refine rel_seq (rel_ctr v.ctr c₁ c₂ (by rw [s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp]))
    (ctr_call v.ctr c₁) (ctr_call v.ctr c₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19] (by rw [e₁.sp, e₂.sp, s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp])
    (by agree_tac [e₁.saved .x19 (by decide) (by decide), e₂.saved .x19 (by decide) (by decide), y₁, y₂])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

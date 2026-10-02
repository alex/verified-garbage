import VerifiedGarbage.Proof.AesGcm.AArch64.Fn

/-!
# AES-GCM on AArch64: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_aes_expand_key`, then the hash subkey `CIPH_K(0¹²⁸)` at byte 240 from
`vg_aes_ctr32` over a zero block with a zero counter block (`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr ctxH)

theorem rounds_of_len {L : Nat} (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    BitVec.ofNat 64 L >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- `vg_aes_gcm_init`. -/
theorem init_wp (v : GcmImpl) {s : State} (hp : initAArch64.pre s) :
    WP isa (init v.callees) s fun s' => GprAbi s s' ∧ initAArch64.post s s' := by
  simp only [initAArch64] at hp ⊢
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, wc, ws, hL⟩ := hp
  generalize hK : s.gpr .x0 = K at *
  generalize hLn : (s.gpr .x1).toNat = L at *
  generalize hCtx : s.gpr .x2 = Ctx at *
  generalize hW : s.gpr .x3 = W at *
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
  generalize hRd : Spec.Aes.rounds (L / 4) = R at x22₂
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases hL with rfl | rfl | rfl <;> decide
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR' with rfl | rfl | rfl <;> decide
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := covers_off pW (by decide) (by decide)
  have kc : KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L := by
    refine ⟨x0₂, x1₂, x2₂, x3₂, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
      d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩
    · rw [rd₂', wr₂', hrd]
      exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
        (covers_left (covers_cons (covers_prefix pC (by decide)) pS))
    · rw [wr₂']; exact covers_cons (covers_prefix pC (by decide)) pS
  refine WP.seq (WP.mono (key_call v.key kc) fun s₃ g => ?_)
  have g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  have g21 : s₃.gpr .x21 = Ctx := by rw [g.saved .x21 (by decide) (by decide), x21₂]
  have g22 : s₃.gpr .x22 = BitVec.ofNat 64 R := by rw [g.saved .x22 (by decide) (by decide), x22₂]
  have rd₃ : s₃.rd = s.rd := g.rd.trans rd₂'
  have wr₃ : s₃.wr = s.wr := g.wr.trans wr₂'
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, x0₄, x1₄, x2₄, x3₄, x4₄, x5₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 248) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 104) (0 : BitVec 64) ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .x3 = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₄.gpr .x5 = W + BitVec.ofNat 64 512 ∧ Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] s₃ s₄ ∧
      s₄.sp = s₃.sp ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [g19, g21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, g21]
    · simp [gpr_write, g22]
    · simp [gpr_write, g19]
    · simp [gpr_write, g21]
    · simp [gpr_write]
    · simp [gpr_write, g19]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have rd₄' : s₄.rd = s.rd := rd₄.trans rd₃
  have wr₄' : s₄.wr = s.wr := wr₄.trans wr₃
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have e248 : Ctx + BitVec.ofNat 64 248 = Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 240 8).symm
  have e104 : W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 96 8).symm
  rw [e248, e104] at hm₄
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Proof.Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store2 _ _ _).mono (by simp))
  have hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  have hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have hk₄ : bytesAt s₄.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0.sub_left (Region.sub_prefix hRb)
        · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))) (by omega),
      ← hRd, g.out, m₂, bytesAt_frame fsv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Lay.wSub (by decide)))
        (by rcases hL with rfl | rfl | rfl <;> decide)]
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄']; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄']; exact pW
  have cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 := by
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
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun s₅ c => ?_)
  have gout := c.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  have c19 : s₅.gpr .x19 = W := by rw [c.saved .x19 (by decide) (by decide), og₄ _ (by decide), g19]
  have dSv : ∀ r ∈ [(⟨Ctx, 240⟩ : Region), ⟨W + BitVec.ofNat 64 512, 512⟩], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)) |>.symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have hsv₁ : SavedAt s₁.mem W s := by rw [m₁]; exact savedAt_save _ _ _
  have hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← m₂]; exact g.frame) dSv).frame f₄ dSv₄).frame c.frame dSv₅)
  refine WP.mono (exit_ok c19 (by rw [c.sp, sp₄, g.sp, sp₂, sp₁])
    (by rw [c.rd, c.wr, wr₄']; exact covers_left pW) hsv₅) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  rw [hm]
  refine ⟨?_, ?_⟩
  · rw [length_bytesAt, hRd, bytesAt_frame c.frame (fun r hr => ?_) (by omega), hk₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    · exact dK0.sub_left (Region.sub_prefix hRb)
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
  · show blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = _
    rw [gout.1, Spec.Gcm.aes, length_bytesAt, hRd]
    simp

end VG.Proof.AesGcm.AArch64

import VerifiedGarbage.Proof.AesGcm.X86_64.Contract

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_aes_expand_key`, then the hash subkey `CIPH_K(0¹²⁸)` at byte 240 from
`vg_aes_ctr32` over a zero block with a zero counter block (`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr ctxH)

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- `vg_aes_gcm_init`. -/
theorem init_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.initX86_64.pre s) :
    WP isa (init v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.initX86_64.post s s' := by
  simp only [Proof.AesGcm.initX86_64, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, r_c, r_s, k_k, k_c, k_s, wc, ws, hL⟩ := hp
  generalize hK : s.gpr .rdi = K at *
  generalize hLn : (s.gpr .rsi).toNat = L at *
  generalize hCtx : s.gpr .rdx = Ctx at *
  generalize hW : s.gpr .rcx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .rcx hW pW
  have hsi : s.gpr .rsi = BitVec.ofNat 64 L := by rw [← hLn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hR : BitVec.ofNat 64 L >>> 2 + 6#64 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
    rcases hL with rfl | rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h15, h13, hbx, hcx, hdi, hsi₂, hdx, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi), .shift .shr .rbx 2,
        .alu .add .rbx (imm 6)] ++ ptr .rcx .r15 scrO) s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rbx = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 512 ∧ s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 L ∧
      s₂.gpr .rdx = Ctx ∧ s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, hg₁, hW, hCtx, hK, hsi, hSP, hR]
  generalize hRd : Spec.Aes.rounds (L / 4) = R at hbx
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases hL with rfl | rfl | rfl <;> decide
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR' with rfl | rfl | rfl <;> decide
  refine WP.seq ?_
  rw [List.append_assoc]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  have pS : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] s.wr := covers_off pW (by decide) (by decide)
  have kc : KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L := by
    refine ⟨hdi, hsi₂, hdx, hcx, hL, d_kc.sub_right (Region.sub_prefix (by decide)),
      d_ks.sub_right (Lay.wSub (by decide)), (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), by rw [hsp]; exact k_k, by rw [hsp]; exact k_c.sub_right (Region.sub_prefix (by decide)),
      by rw [hsp]; exact k_s.sub_right (Lay.wSub (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂, hrd]
      exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
        (covers_left (covers_cons (covers_prefix pC (by decide)) pS))
    · rw [wr₂]; exact covers_cons (covers_prefix pC (by decide)) pS
  refine WP.seq (WP.mono (key_call v.key kc) fun s₃ g => ?_)
  have g15 : s₃.gpr .r15 = W := by rw [g.saved .r15 (by decide), h15]
  have g13 : s₃.gpr .r13 = Ctx := by rw [g.saved .r13 (by decide), h13]
  have gbx : s₃.gpr .rbx = BitVec.ofNat 64 R := by rw [g.saved .rbx (by decide), hbx]
  have gsp : s₃.gpr .rsp = SP := by rw [g.saved .rsp (by decide), hsp]
  have rd₃ : s₃.rd = s.rd := g.rd.trans rd₂
  have wr₃ : s₃.wr = s.wr := g.wr.trans wr₂
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .rbx)] ++ ptr .rdx .r15 tO ++ ptr .rcx .r13 240 ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO) s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = BitVec.ofNat 64 R ∧ s₄.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s₄.gpr .rcx = Ctx + BitVec.ofNat 64 240 ∧ s₄.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₄.gpr .r9 = W + BitVec.ofNat 64 512 ∧ (∀ r ∈ calleeSaved, s₄.gpr r = s₃.gpr r) ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    rw [add_ofNat_assoc, add_ofNat_assoc]
    refine ⟨_, by xrun [g15, g13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags, gbx]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have g4sp : s₄.gpr .rsp = SP := by rw [hg₄ .rsp (by decide), gsp]
  have rd₄ : s₄.rd = s.rd := hrd₄.trans rd₃
  have wr₄ : s₄.wr = s.wr := hwr₄.trans wr₃
  -- The disjointness of the parts.
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub he)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega)
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Cmac.frame_store2 _ _ _).mono (by simp))
  have hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  have hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  have hk₄ : bytesAt s₄.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0.sub_left (Region.sub_prefix hRb)
        · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))) (by omega),
      ← hRd, g.out, hm₂, bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Lay.wSub (by decide)))
        (by rcases hL with rfl | rfl | rfl <;> decide)]
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  have cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 := by
    refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, h8₄, h9₄, hR', ?_, ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega
    · simpa using dCW 0 240 (by decide) 96 16 (by decide)
    · simpa using dCW 0 240 (by decide) 512 2048 (by decide)
    · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact dCW 240 16 (by decide) 512 2048 (by decide)
    · rw [g4sp]; exact k_c.sub_right (Region.sub_prefix (by decide))
    · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
    · rw [g4sp]; exact k_c.sub_right (Offset.sub_base _ (by decide))
    · rw [g4sp]; exact k_s.sub_right (Lay.wSub (by decide))
    · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
        (covers_left (covers_off pW' (by decide) (by decide))) (covers_cons
        (covers_left (covers_off pC' (by decide) (by decide))) (covers_left (covers_off pW' (by decide) (by decide)))))
    · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_cons (covers_off pC' (by decide) (by decide))
        (covers_off pW' (by decide) (by decide)))
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun s₅ c => ?_)
  have gout := c.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  have c15 : s₅.gpr .r15 = W := by rw [c.saved .r15 (by decide), hg₄ .r15 (by decide), g15]
  have c5sp : s₅.gpr .rsp = SP := by rw [c.saved .rsp (by decide), g4sp]
  have cfr := c.frame
  rw [g4sp] at cfr
  -- The saved registers and the return address.
  have dSv : ∀ r ∈ [(⟨Ctx, 240⟩ : Region), ⟨W + BitVec.ofNat 64 512, 512⟩, below SP 8], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)) |>.symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (k_s.sub_right (Lay.wSub (by decide))).symm
  have dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩, below SP 8], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact (k_s.sub_right (Lay.wSub (by decide))).symm
  have hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← hm₂]; exact g.frame) (by rw [hsp]; exact dSv)).frame f₄ dSv₄).frame cfr dSv₅)
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept cfr (fun r hr => ?_), ret_kept f₄ (fun r hr => ?_), ret_kept g.frame (fun r hr => ?_), hm₂,
      ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_s.sub_right (Lay.wSub (by decide))
    · rw [hsp] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact r_c.sub_right (Region.sub_prefix (by decide))
      · exact r_s.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact r_s.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Lay.wSub (by decide))
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact r_s.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
  refine WP.mono (exit_ok c15 (by rw [c5sp, hSP]) (by rw [c.rd, c.wr, wr₄]; exact covers_left pW) hsv₅
    (by rw [hSP, hret])) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  simp only [Proof.AesGcm.initX86_64]
  rw [hK, hLn, hCtx, hm]
  refine ⟨?_, ?_⟩
  · rw [length_bytesAt, hRd, bytesAt_frame cfr (fun r hr => ?_) (by omega), hk₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    · exact dK0.sub_left (Region.sub_prefix hRb)
    · exact (d_cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    · exact (k_c.sub_right (Region.sub_prefix (by omega))).symm
  · rw [ctxH_eq, gout.1, Spec.Gcm.aes, length_bytesAt, hRd]
    simp

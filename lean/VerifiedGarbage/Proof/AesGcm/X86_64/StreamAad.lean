import VerifiedGarbage.Proof.AesGcm.X86_64.Contract

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The additional data absorbed
into GHASH (`absorb 16`), for any additional data so far of the length
`aad_len` gives modulo 16 (`streamAad_run`), and so for all of them
(`streamAad_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

theorem ctxH_eq (m : Mem) (p : Addr) : ctxH m p = blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

/-- The layout, from disjointness of the context, the state, `W` and the stack. -/
theorem Lay.of {Ctx St W SP : Addr} (cw : Ctx.toNat + 256 ≤ 2 ^ 64) (sw : St.toNat + 80 ≤ 2 ^ 64)
    (ww : W.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩)
    (cW : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩) (sW : (⟨St, 80⟩ : Region).Disjoint ⟨W, 2560⟩)
    (kc : (below SP 8).Disjoint ⟨Ctx, 256⟩) (ks : (below SP 8).Disjoint ⟨St, 80⟩)
    (kw : (below SP 8).Disjoint ⟨W, 2560⟩) : Lay Ctx St W SP :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide)),
    kc, ks, kw⟩

/-- The regions `vg_aes_gcm_stream_aad` writes. -/
abbrev aadFrame (St W SP : Addr) : List Region := [⟨St + BitVec.ofNat 64 16, 32⟩, ⟨W, 2560⟩, below SP 8]

/-- One run, for additional data so far `x` (of `aad_len` bytes modulo 16). -/
theorem streamAad_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamAadX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .rdx).toNat % 16) :
    WP isa (streamAad v.callees) s fun s' => gprPreserved s s' ∧
      Frame (aadFrame (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp)) s.mem s'.mem ∧
      (Absorbed s.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .rdi)) x →
        Absorbed s'.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .rdi)) (x ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)) := by
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_ds, d_dw, d_sw, r_s, r_w, k_c, k_d, k_s, k_w, wc, wd, ws, ww⟩ := hp
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rsi = St at *
  generalize hD : s.gpr .rcx = D at *
  generalize hW : s.gpr .r9 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hn : (s.gpr .r8).toNat = n at *
  have L : Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .r9 hW pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rcx),
        .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧
      s₂.gpr .rbp = BitVec.ofNat 64 n ∧ s₂.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧
      s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hand := and15 (s.gpr .rdx)
    rw [imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁, hW]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hD]
    · simp [gpr_setReg, hg₁, ← hn]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg₁, hand, hx]
    · simp [gpr_setReg, gpr_arithFlags, hg₁, hSP]
    all_goals rfl
  have he₂ : Env Ctx St W SP s₂ := ⟨h13, h14, h15, hg₂, by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
    · exact pW⟩
  have dsv : ∀ r ∈ [savedR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact d_dw.sub_right (Lay.wSub (by decide))
  have hdata : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [hm₂]; exact bytesAt_frame f₁ dsv (by omega)
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [hm₂, ctxH_eq, blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)]
  have rdD : Covers [⟨D, n⟩] (s₂.rd ++ s₂.wr) := by
    rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hai : AbsIn Ctx St W SP 16 (ctxH s.mem Ctx) x D n s₂ :=
    ⟨he₂, h12, hbp, hbx, ⟨rdD, by have := (s.gpr .r8).isLt; omega, wd, d_ds, d_dw, k_d⟩, hH⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (absorb_ok v L (yo := 16) (.inr rfl) hai) fun s₃ ho => ?_)
  have he₃ := ho.env
  have hsv₃ : SavedAt s₃.mem W s := (hm₂ ▸ hsv₁).frame ho.frame (saved_absFrame L (.inr rfl))
  obtain ⟨s₄, run₄, hsv, hother, hm₄, hrd₄, hwr₄⟩ := restore_ok s₃ he₃.r15 (covers_left he₃.perm.w) hsv₃
  refine WP.of_runBlock ⟨s₄, run₄, ⟨?_, ?_⟩, ?_, fun ha => ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.rbx, 128) (by simp [saved])
    · exact hsv (.rbp, 136) (by simp [saved])
    · rw [hother .rsp (by simp [saved]), he₃.rsp, hSP]
    · exact hsv (.r12, 144) (by simp [saved])
    · exact hsv (.r13, 152) (by simp [saved])
    · exact hsv (.r14, 160) (by simp [saved])
    · exact hsv (.r15, 168) (by simp [saved])
  · rw [hm₄, hSP, ret_kept ho.frame (fun r hr => ?_), hm₂, ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Lay.stSub (by decide))
      · exact r_s.sub_right (Lay.stSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
  · rw [hm₄]
    refine ((f₁.sub fun r hr => ?_).trans (hm₂ ▸ ho.frame.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · have dS : ∀ r ∈ [savedR W], ∀ d k, d + k ≤ 80 → (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
      intro r hr d k hk
      simp only [List.mem_singleton] at hr; subst hr
      exact (d_sw.sub_left (Lay.stSub hk)).sub_right (Lay.wSub (by decide))
    have ha₂ : Absorbed s₂.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH s.mem Ctx) x := by
      rw [hm₂]
      refine ha.congr (blockAt_frame f₁ fun r hr => dS r hr 16 16 (by decide)) (bytesAt_frame f₁
        (fun r hr => dS r hr 32 (x.length % 16) (by omega)) (by omega))
    rw [hm₄, ← hdata]
    exact ho.abs ha₂

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

/-- `vg_aes_gcm_stream_aad`. -/
theorem streamAad_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamAadX86_64.pre s) :
    WP isa (streamAad v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamAadX86_64.post s s' := by
  have h₀ := streamAad_run v hp (x := List.replicate ((s.gpr .rdx).toNat % 16) 0) (by simp)
  have h := WP.forall_det (P := fun a : List Byte => a.length % 16 = (s.gpr .rdx).toNat % 16)
    (R := fun s' => gprPreserved s s' ∧ Frame (aadFrame (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp)) s.mem s'.mem)
    (WP.mono h₀ fun _ h => ⟨h.1, h.2.1⟩) fun a ha => WP.mono (streamAad_run v hp ha) fun _ h => h.2.2
  refine WP.mono h fun s' ⟨⟨hg, hf⟩, hq⟩ => ⟨hg, fun ciph iv a hr hl => ?_⟩
  have hp' := hp
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp'
  obtain ⟨-, -, -, -, -, -, d_sw, -, -, -, -, k_s, -, -, -, ws, -⟩ := hp'
  generalize s.gpr .rsi = St at *
  have dS : ∀ d k, (d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ aadFrame St (s.gpr .r9) (s.gpr .rsp),
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact d_sw.sub_left (Lay.stSub (by omega))
    · exact (k_s.sub_right (Lay.stSub (by omega))).symm
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · rw [← hj]; simpa using blockAt_frame hf (dS 0 16 (.inl (by decide)))
  · rw [Proof.Gcm.ghashInput_nil] at ha ⊢
    refine hq a ?_ ha
    rw [hl, toNat_mod16]
  · exact hc.congr (blockAt_frame hf (dS 48 16 (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame hf (dS 64 16 (.inr ⟨by decide, by decide⟩)))

end VG.Proof.AesGcm.X86_64

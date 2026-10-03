import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The entry and `front_ok`
start the state at `W + 16` and absorb the additional data; `encBody`
encrypts the data and absorbs the ciphertext, and `finBody 0` writes the tag
to `W` (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem slots_bodyFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact slots_absFrame L r hr

theorem saved_bodyFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact saved_tFrame L (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact saved_absFrame L (.inr rfl) r hr

theorem st0_bodyFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
      · exact st0_w L ⟨by decide, by decide⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `finPrep`: the lengths from their slots. -/
theorem finPrep_ok {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr))
    {al n : Nat} (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block finPrep) s fun s' => s'.gpr .x26 = BitVec.ofNat 64 al ∧ s'.gpr .x27 = BitVec.ofNat 64 n ∧
      Regs [.x26, .x27] s s' := by
  have q₁ := in_off hr (show 224 + 8 ≤ 2560 by decide) (by decide)
  have q₂ := in_off hr (show 240 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by simp only [finPrep]; arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]; rfl

theorem seal_wp (v : GcmImpl) {s : State} (hs : sealAArch64.pre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  have ol := oneLay (Nat.le_refl 1) hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have h3 := ofNat_toNat' (s.gpr .x3)
  have h5 := ofNat_toNat' (s.gpr .x5)
  have h7 := ofNat_toNat' (s.gpr .x7)
  generalize hW : stackArg s 0 = W at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  have hRb : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRR]; exact hR
  have hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x7).isLt
  refine WP.seq (WP.mono (oneEntry_ok hW hsp hCtx perm)
    fun s₁ ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, sl₁, sl₂, sl₃, sl₄, f₁, sv₁, rd₁, wr₁⟩ => ?_)
  rw [hA] at sl₁
  rw [← h5] at sl₂
  rw [hD] at sl₃
  rw [← h7] at sl₄
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  have kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  have hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np nl :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩
  have haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al :=
    ⟨by rw [rd₁, wr₁]; exact aR, hal ▸ (s.gpr .x5).isLt, wa, daW.sub_right sub16, daW⟩
  have iv₁ : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega)
  have a₁ : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) daW) (by omega)
  refine front_ok L v he₁ (fun _ _ => rfl : Kept s₁.gpr s₁) (x23₁.trans hNp) (by rw [x24₁, ← h3])
    (by rw [x26₁, ← h3]) x27₁ hnon haad hH₁ sl₁ sl₂ sl₃ sl₄ fun s₂ h₂ => ?_
  rw [iv₁, a₁] at h₂
  have x22₂ : s₂.gpr .x22 = BitVec.ofNat 64 R := by rw [h₂.x22, x22₁, ← hRR, ofNat_toNat']
  have hdat₂ : DataW Ctx (W + BitVec.ofNat 64 16) W s₂ D n :=
    ⟨⟨covers_left (by rw [h₂.wr, wr₁]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩,
      by rw [h₂.wr, wr₁]; exact dW, dcd⟩
  have hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W s.sp s₂.gpr R n 0 D (bytesAt s.mem A al) [] (ctxH s.mem Ctx) s₂ :=
    ⟨h₂.env, fun _ _ => rfl, x22₂, hRb, h₂.x25, h₂.x26, h₂.x27, h₂.x28, rfl, by decide, hdat₂, h₂.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (encBody_ok L v hB (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx)
    (bytesAt s.mem Np nl))))) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_)
  obtain ⟨o₁, o₂, o₃⟩ := h₃.post h₂.abs (Proof.Gcm.ctr_zero _ _ _ _ h₂.cb)
  have sL₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al := by
    rw [slot_kept h₃.frame (slots_bodyFrame L ddW) (by decide) (by decide),
      slot_kept h₂.frame (slots_frontFrame L) (by decide) (by decide), sl₂]
  have sN₃ : s₃.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n := by
    rw [slot_kept h₃.frame (slots_bodyFrame L ddW) (by decide) (by decide),
      slot_kept h₂.frame (slots_frontFrame L) (by decide) (by decide), sl₄]
  refine WP.seq (WP.mono (finPrep_ok h₃.env.x19 (covers_left h₃.env.perm.w) sL₃ sN₃) fun s₄ ⟨x26₄, x27₄, r₄⟩ => ?_)
  have he₄ := h₃.env.of_regs r₄
  have x22₄ : s₄.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₄.others _ (by decide), h₃.kept .x22 (by decide), x22₂]
  have kcd : ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨Ctx, 256⟩ : Region).Disjoint r :=
    keep_body dcW dcd
  have hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame h₃.frame kcd hRb, ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW) hRb,
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW) hRb]
  have hD₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [bytesAt_frame h₂.frame (keep_of_sub (frontFrame_work W) ddW) (by omega),
      bytesAt_frame f₁ (keep_of_sub (entryR_work W) ddW) (by omega)]
  have hc₂ : ciphOf s₂.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW) hRb,
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW) hRb]
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [r₄.mem, blockAt_frame h₃.frame fun r hr => (kcd r hr).sub_left (Lay.ctxSub (by decide)), h₂.hH]
  have hlen : ([] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n)).length = n := by
    rw [List.nil_append, Proof.Gcm.length_xorKs, length_bytesAt]
  refine WP.seq (WP.mono (finBody_ok L v (.inl rfl) (a := bytesAt s.mem A al) (H := ctxH s.mem Ctx)
    (c := [] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n))
    he₄ (fun _ _ => rfl) x22₄ hRb (by rw [x26₄, length_bytesAt]) (by rw [x27₄, hlen]) (by rw [hlen]; exact hnlt)
    hH₄) fun s₅ ⟨he₅, _, f₅, out₅⟩ => ?_)
  have sv₅ : SavedAt s₅.mem W s := by
    have := (sv₁.frame h₂.frame (saved_frontFrame L)).frame h₃.frame (saved_bodyFrame L ddW)
    rw [← r₄.mem] at this
    exact this.frame f₅ (saved_finFrame L (.inl rfl))
  refine WP.mono (exit_ok he₅.x19 he₅.sp (covers_left he₅.perm.w) sv₅) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  rw [hm]
  have hdata : bytesAt s₅.mem D n = gctr (ctxCiph s.mem Ctx R)
      (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₅ (keep_of_sub (finFrame_work W (.inl rfl)) ddW) (by omega), r₄.mem, o₃, hc₂, hD₂,
      Proof.Gcm.gctr_eq]
    rfl
  have hj₄ : blockAt s₄.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl) := by
    rw [r₄.mem, blockAt_frame h₃.frame (st0_bodyFrame L ddW), h₂.j0]
  have htag := out₅ (by rw [r₄.mem]; exact o₁)
  rw [add_ofNat_zero, r₄.mem, hc₃, ← r₄.mem, hj₄] at htag
  have he : [] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n) = gctr (ctxCiph s.mem Ctx R)
        (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [List.nil_append, hc₂, hD₂, Proof.Gcm.gctr_eq]; rfl
  rw [he] at htag
  rw [hdata, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])]
  rfl

end VG.Proof.AesGcm.AArch64

import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. After the entry, `tagLenOk`
checks the tag length (a public value); if §5.2.1.2 does not allow it, the
tag is zeroed and 0 returned; otherwise `finBody 112` writes the tag at
`W + 112`, `cmpSeg` compares its first `tag_len` bytes with the received ones
without a branch, and `verMask` keeps it or zeros (`ver_run`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes ctxCiph ctxH zeros)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem tagLenOk_le {t : Nat} (h : Spec.Gcm.tagLenOk t = true) : t ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem setWidth_ofNat_bool (b : Bool) :
    (BitVec.ofNat 64 (if b then 1 else 0)).setWidth 32 = if b then 1 else 0 := by
  cases b <;> rfl

/-- The tag zeroed when its length is not allowed. -/
theorem zeroTag_ok {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block [imm .x9 0, .str .x .x9 .x19 0, .str .x .x9 .x19 8, imm .x0 0]) s fun s' =>
      s'.gpr .x0 = 0 ∧ bytesAt s'.mem W 16 = zeros 16 ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      Others [.x0, .x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₁ := in_off hw (show 0 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hw (show 8 + 8 ≤ 2560 by decide) (by decide)
  obtain ⟨s', run, hm, x0', og, sp', rd', wr'⟩ : ∃ s', runBlock isa
      [imm .x9 0, .str .x .x9 .x19 0, .str .x .x9 .x19 8, imm .x0 0] s = some s' ∧
      s'.mem = (s.mem.writeW W (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .x0 = 0 ∧ Others [.x0, .x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by arun [h19, w₁, w₂], ?_⟩
    refine ⟨?_, by simp [gpr_write], by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, BitVec.add_zero]; rfl
  refine WP.of_runBlock ⟨s', run, x0', ?_, ?_, og, sp', rd', wr'⟩
  · rw [hm]; exact zeroT_bytes _ _
  · rw [hm]; exact Proof.Cmac.frame_store2 _ _ _

/-- The regions `verify` writes. -/
abbrev verFrame (St W : Addr) : List Region :=
  savedR W :: ⟨W, 16⟩ :: finFrame St W 112 ++ [⟨W + BitVec.ofNat 64 256, 32⟩]

/-- One run of `stream_verify`, for a message `a`, `c` of those lengths. -/
theorem ver_run (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x3 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x4 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        let T := toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2)))
        if Spec.Gcm.tagLenOk (s.gpr .x6).toNat ∧ T.take (s.gpr .x6).toNat =
            bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat then
          (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x5) 16 = T
        else (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x5) 16 = zeros 16) := by
  have hs' : finPre s := hs
  obtain ⟨L, perm, hR⟩ := lay_of_fin hs'
  generalize hT : toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
      [ofBytes (lensBlock a.length c.length)] ^^^
      ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2))) = T
  generalize htl : (s.gpr .x6).toNat = tl
  have htl' : tl < 2 ^ 64 := htl ▸ (s.gpr .x6).isLt
  -- The entry.
  refine WP.seq (WP.block_append (WP.mono (finEntry_ok rfl rfl rfl perm)
    fun s₁ ⟨he₁, hk₁, x22₁, x26₁, x27₁, x6₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂, run₂, x28₂, r₂⟩ : ∃ s₂, runBlock isa [mov .x28 .x6] s₁ = some s₂ ∧
      s₂.gpr .x28 = BitVec.ofNat 64 tl ∧ Regs [.x28] s₁ s₂ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, x6₁, ← htl], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ := he₁.of_regs r₂
  have fsv : Frame [savedR (s.gpr .x5)] s.mem s₂.mem := by rw [r₂.mem, m₁]; exact savedMem_frame _ _ _
  obtain ⟨hc₁, hj₁, hH₁, hA₁⟩ := fin_inv hs' fsv (x := ghashInput a c)
  have hk₂ : Kept s₂.gpr s₂ := fun _ _ => rfl
  refine WP.seq (WP.mono (tagLenOk_ok s₂ x28₂ htl') fun s₃ ⟨x9₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have x22₃ : s₃.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [r₃.others _ (by decide), r₂.others _ (by decide), x22₁]
  have x26₃ : s₃.gpr .x26 = BitVec.ofNat 64 a.length := by
    rw [r₃.others _ (by decide), r₂.others _ (by decide), x26₁, h3]
  have x27₃ : s₃.gpr .x27 = BitVec.ofNat 64 c.length := by
    rw [r₃.others _ (by decide), r₂.others _ (by decide), x27₁, h4]
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have sv₃ : SavedAt s₃.mem (s.gpr .x5) s := by
    have := savedAt_save s.mem (s.gpr .x5) s
    rwa [← m₁, ← r₂.mem, ← m₃] at this
  have ev : isa.eval (.zero .x .x9) s₃ =
      some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env (s.gpr .x0) (s.gpr .x2) (s.gpr .x5) s.sp s₄ ∧
      SavedAt s₄.mem (s.gpr .x5) s ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        if Spec.Gcm.tagLenOk tl ∧ T.take tl = bytesAt s.mem (s.gpr .x5) tl then
          (s₄.gpr .x0).setWidth 32 = 1 ∧ bytesAt s₄.mem (s.gpr .x5) 16 = T
        else (s₄.gpr .x0).setWidth 32 = 0 ∧ bytesAt s₄.mem (s.gpr .x5) 16 = zeros 16))
    (WP.ite _ ev (fun ht => ?_) (fun hf => ?_)) fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.mono (zeroTag_ok he₃.x19 he₃.perm.w) fun s₄ ⟨x0₄, z₄, f₄, og₄, sp₄, rd₄, wr₄⟩ =>
      ⟨he₃.keep (fun r hr => og₄ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄, sv₃.frame f₄ (saved_tag16 L), fun _ => ?_⟩
    rw [ite_eq_right (by simp [hok])]
    exact ⟨by rw [x0₄]; rfl, z₄⟩
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := tagLenOk_le hok
    refine WP.seq (WP.mono (finBody_ok L v (.inr rfl) (a := a) (c := c) (H := ctxH s.mem (s.gpr .x0)) he₃ hk₃ x22₃ hR x26₃ x27₃ hc
      (by rw [m₃]; exact hH₁)) fun s₄ ⟨he₄, hk₄, f₄, out₄⟩ => ?_)
    have x28₄ : s₄.gpr .x28 = BitVec.ofNat 64 tl := (hk₄ .x28 (by decide)).trans x28₂
    refine WP.seq (WP.mono (cmpSeg_ok L he₄ hk₄ x28₄ hle) fun s₅ ⟨x10₅, he₅, hk₅, _, f₅⟩ => ?_)
    refine WP.mono (verMask_ok L he₅ hk₅
      (b := decide (bytesAt s₄.mem (s.gpr .x5 + BitVec.ofNat 64 112) tl = bytesAt s₄.mem (s.gpr .x5) tl))
      (by rw [x10₅]; by_cases hp : bytesAt s₄.mem (s.gpr .x5 + BitVec.ofNat 64 112) tl =
            bytesAt s₄.mem (s.gpr .x5) tl <;> simp [hp]))
      fun s₆ ⟨x0₆, w₆, he₆, _, _, f₆⟩ =>
        ⟨he₆, ((sv₃.frame f₄ (saved_finFrame L (.inr rfl))).frame f₅ (saved_cmp L)).frame f₆ (saved_tag16 L),
          fun ha => ?_⟩
    have hT₄ : bytesAt s₄.mem (s.gpr .x5 + BitVec.ofNat 64 112) 16 = T := by
      rw [out₄ (by rw [m₃]; exact hA₁ ha), m₃, hc₁, hj₁, ← hT]
    have hW₄ : bytesAt s₄.mem (s.gpr .x5) tl = bytesAt s.mem (s.gpr .x5) tl := by
      have dW : ∀ r ∈ finFrame (s.gpr .x2) (s.gpr .x5) 112, (⟨s.gpr .x5, tl⟩ : Region).Disjoint r := by
        intro r hr
        refine Region.Disjoint.sub_left ?_ (Region.sub_prefix hle)
        have ww : ∀ e j, 16 ≤ e → e + j ≤ 2560 →
            (⟨s.gpr .x5, 16⟩ : Region).Disjoint ⟨s.gpr .x5 + BitVec.ofNat 64 e, j⟩ := fun e j h₁ h₂ => by
          simpa using L.w_w (a := 0) (n := 16) (d := e) (k := j) (.inl h₁) (by decide) h₂
        rcases List.mem_append.mp hr with hr | hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact (L.sa.sub_left (Lay.stSub (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact (L.sa.sub_left (Region.sub_prefix (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
      rw [bytesAt_frame f₄ dW (by omega), m₃]
      refine bytesAt_frame fsv (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact (saved_tag16 L _ (List.mem_singleton_self _)).symm.sub_left (Region.sub_prefix hle)
    have hT₅ : bytesAt s₅.mem (s.gpr .x5 + BitVec.ofNat 64 112) 16 = T := by
      rw [bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hT₄]
    have hb : (bytesAt s₄.mem (s.gpr .x5 + BitVec.ofNat 64 112) tl = bytesAt s₄.mem (s.gpr .x5) tl) ↔
        T.take tl = bytesAt s.mem (s.gpr .x5) tl := by
      rw [← bytesAt_take _ _ hle, hT₄, hW₄]
    by_cases hp : T.take tl = bytesAt s.mem (s.gpr .x5) tl
    · rw [ite_eq_left ⟨hok, hp⟩]
      have hb' := hb.mpr hp
      simp only [hb', decide_true, ite_true] at x0₆ w₆
      exact ⟨by rw [x0₆]; rfl, by rw [w₆, hT₅]⟩
    · rw [ite_eq_right (fun h => hp h.2)]
      have hb' : ¬ (bytesAt s₄.mem (s.gpr .x5 + BitVec.ofNat 64 112) tl = bytesAt s₄.mem (s.gpr .x5) tl) :=
        fun h => hp (hb.mp h)
      simp only [hb', decide_false, Bool.false_eq_true, ite_false] at x0₆ w₆
      exact ⟨by rw [x0₆]; rfl, w₆⟩
  refine WP.mono (exit_ok he₄.x19 he₄.sp (covers_left he₄.perm.w) sv₄) fun s' ⟨ga, hm, hx0, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hm, hx0]
  exact post₄ ha

theorem streamVerify_wp (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧ streamVerifyAArch64.post s s' := by
  have h3 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x4 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x4).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x4).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  let tl := (s.gpr .x6).toNat
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' =>
      if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2).take tl = bytesAt s.mem (s.gpr .x5) tl then
        (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x5) 16 = Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2
      else (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x5) 16 = zeros 16)
    (ver_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x4 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (ver_run v hs hl h4c (hc ▸ (s.gpr .x4).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have ht : Spec.Gcm.fullTag ciph h iv a c =
      toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
        [ofBytes (lensBlock a.length c.length)] ^^^
        ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2))) := by
    rw [Proof.Gcm.fullTag_eq, hj]; rfl
  show if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h iv a c).take tl = _ then _ else _
  rw [ht]
  exact hout habs

end VG.Proof.AesGcm.AArch64

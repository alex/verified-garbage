import VerifiedGarbage.Proof.AesGcm.Arm.TextAbsorb

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. Both save our caller's
registers in `scratch` (`W`); `encrypt` XORs the keystream into the data
(`crypt`) and then absorbs the ciphertext into GHASH (`textAbsorb`), and
`decrypt` the other way round (`streamEncrypt_wp`, `streamDecrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 j0)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem scLay {s₀ : State} (h : streamCryptPre s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp := by
  obtain ⟨-, -, dcs, -, dcW, -, dsW, -, -, -, -, bc, bs, -, bW, fc, fs, -, fW, sp8, -, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- The rounds, as `r1` holds them. -/
abbrev scR (s₀ : State) : Nat := (s₀.gpr .r1).toNat

/-- After the entry, from `s₀`. -/
structure SC1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  args : ArgsKeep 7 s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ 6) s₀
  frame : Frame [savedR (arg s₀ 6)] s₀.mem s₁.mem

theorem sc_argsW {s₀ : State} (h : streamCryptPre s₀) : ∀ r ∈ [savedR (arg s₀ 6)], (args s₀ 7).Disjoint r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm

theorem sc1_wp {s₀ : State} (h : streamCryptPre s₀) {Q : State → Prop} (k : ∀ s₁, SC1 s₀ s₁ → Q s₁) :
    WP isa (.block cryptEntry) s₀ Q := by
  have hA := sc_argsW h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r2), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 6), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha : ∀ i < 7, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => arg_in (n := 7) hi spf (by rw [hrd]; simp)
  refine entry_ok (off := 24) (by decide) (ha 6 (by decide)) fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : ArgsKeep 7 s₀ s₁ := (ArgsKeep.refl 7 s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem textArgs_run {s₀ s : State} (hk : ArgsKeep 7 s₀ s) (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32)
    (hin : args s₀ 7 ∈ s₀.rd) :
    ∃ s', runBlock isa textArgs s = some s' ∧
      s'.gpr .r4 = arg s₀ 4 ∧ s'.gpr .r5 = arg s₀ 5 ∧ s'.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨i4, v4⟩ := hk.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨i5, v5⟩ := hk.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨i2, v2⟩ := hk.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  refine ⟨_, by simp only [textArgs]; arun [i4, v4, i5, v5, i2, v2], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v4]
  · simp [gpr_setReg, v5]
  · simp only [gpr_setReg, ite_true, v2, and15]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  · exact ⟨rfl, rfl, rfl, rfl⟩

section
variable {s₀ : State} (h : streamCryptPre s₀)
include h

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {k7 : BitVec 32} {s : State} (hk : ArgsKeep 7 s₀ s) :
    DataW (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s (arg s₀ 4) (arg s₀ 5).toNat := by
  obtain ⟨hrd, hwr, -, dcD, -, dsD, -, -, dDW, -, -, -, -, bD, -, -, -, fD, -, -, -, -⟩ := h
  have hD : Covers [⟨State.addr (arg s₀ 4), (arg s₀ 5).toNat⟩] s.wr := by
    rw [hk.wr, hwr]; exact covers_of_mem (by simp)
  exact ⟨⟨covers_left hD, (arg s₀ 5).isLt, fD, dsD.symm, dDW, bD⟩, hD, dcD⟩

/-- The input of `crypt`, for `P` bytes of text so far. -/
theorem sc_crIn {k7 : BitVec 32} {s : State} (he : Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s)
    (hk : ArgsKeep 7 s₀ s) (h4 : s.gpr .r4 = arg s₀ 4) (h5 : s.gpr .r5 = arg s₀ 5)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16)) (icb : Block) {P : Nat}
    (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = P) :
    CrIn (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) (scR s₀) icb P (arg s₀ 4) (arg s₀ 5).toNat s :=
  ⟨he, h4, by rw [h5]; simp, by rw [h6, lowTo_mod16 hP], by rw [he.r8]; simp, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    sc_dataW h hk⟩

/-- The stack arguments are apart from what the pieces write. -/
theorem sc_argsCr : ∀ r ∈ crFrame (s₀.gpr .r2) (arg s₀ 6) s₀.sp (arg s₀ 4) (arg s₀ 5).toNat, (args s₀ 7).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, dsA, -, dDA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dDA.symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

theorem sc_argsTa : ∀ r ∈ taFrame (s₀.gpr .r2) (arg s₀ 6) s₀.sp, (args s₀ 7).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, dsA, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

end

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem stp_crFrame {k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n)
    {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st w sp D n, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega))).symm
  · exact Lay.st_st (.inl h1) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

theorem stp_taFrame {d k : Nat} (hd : d + k ≤ 16 ∨ 48 ≤ d ∧ d + k ≤ 80) :
    ∀ r ∈ taFrame st w sp, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

theorem stp_saved {d k : Nat} (h1 : d + k ≤ 80) :
    ∀ r ∈ [savedR w], (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.st_w h1 (.inr ⟨by decide, by decide⟩)

theorem ctx_saved : ∀ r ∈ [savedR w], (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_taFrame : ∀ r ∈ taFrame st w sp, (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem data_taFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ taFrame st w sp, (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

omit L in
theorem data_saved {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ [savedR w], (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hd.w.sub_right (Lay.wSub (by decide))

theorem saved_taFrame : ∀ r ∈ taFrame st w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
/-- `ciphOf` is `ctxCiph`, and a frame apart from the context keeps it. -/
theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' (State.addr c) R = ctxCiph m (State.addr c) R := ciph_frame hf hd hR

omit L in
theorem ctxH_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) :
    blockAt m' (State.addr c + BitVec.ofNat 64 240) = ctxH m (State.addr c) := by
  rw [ctxH_eq, blockAt_frame hf (fun r hr => (hd r hr).sub_left (Lay.ctxSub (by decide)))]

end

/-- What `encrypt` (or `decrypt`) does, for the counter block `icb`, the
additional data `a` and the text `ct` so far (only their lengths matter to
the code). -/
structure EncOut (s₀ : State) (icb : Block) (a ct : List Byte) (dec : Bool) (s : State) : Prop where
  ctr : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
    Ctr s.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb (ct.length + (arg s₀ 5).toNat)
  out : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
    bytesAt s.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length
        (bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat)
  abs : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
    Absorbed s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) →
    Absorbed s.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghashInput a (ct ++ if dec then bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat else
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length
          (bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat)))
  j : blockAt s.mem (State.addr (s₀.gpr .r2)) = blockAt s₀.mem (State.addr (s₀.gpr .r2))

theorem enc_run {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' := by
  have L := scLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 7 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (WP.block_append (sc1_wp h fun s₁ h1 => ?_))
  obtain ⟨s₂, run₂, h4, h5, h6, hg₂, hK₂⟩ := textArgs_run h1.args spf hin
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hK₂.sp hK₂.rd hK₂.wr
  have hk₂ := h1.args.of_eq hK₂.mem hK₂.sp hK₂.rd hK₂.wr
  have ci := sc_crIn h he₂ hk₂ h4 h5 h6 icb hP
  have hd₂ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₃ hh => ?_)
  obtain ⟨co, rd₃, wr₃, sp₃⟩ := hh
  have hk₃ := hk₂.frame spf co.frame (sc_argsCr h) sp₃ rd₃ wr₃
  have hd₃ := (sc_dataW (k7 := s₀.gpr .r7) h hk₃).ok
  have f₂ : Frame [savedR (arg s₀ 6)] s₀.mem s₂.mem := by rw [hK₂.mem]; exact h1.frame
  have hH₃ : blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide))),
      ctxH_keep f₂ (ctx_saved L)]
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L co.env hk₃ spf hin (sc_argsTa h) hH₃ hd₃ ha hP))
    fun s₄ hh => ?_)
  obtain ⟨ta, rd₄, wr₄, sp₄⟩ := hh
  have sv₄ : SavedAt s₄.mem (arg s₀ 6) s₀ :=
    (((hK₂.mem ▸ h1.saved : SavedAt s₂.mem (arg s₀ 6) s₀)).frame co.frame (saved_crFrame L hd₂)).frame ta.frame
      (saved_taFrame L)
  refine WP.mono (restore_ok ta.env.r11 fW (covers_left ta.env.perm.w) sv₄ ta.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  have hc : ciphOf s₂.mem (State.addr (s₀.gpr .r0)) (scR s₀) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀) :=
    ciph_keep f₂ (ctx_saved L) hR
  have ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P →
      Ctr s₂.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ciphOf s₂.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P :=
    fun hc₀ => by
      rw [hc]
      exact hc₀.congr (blockAt_frame f₂ (stp_saved L (by decide))) (blockAt_frame f₂ (stp_saved L (by decide)))
  have dat₂ : bytesAt s₂.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat :=
    bytesAt_frame f₂ (data_saved hd₂.ok) (by have := hd₂.ok.lt; omega)
  have out₃ : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length →
      bytesAt s₃.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb ct.length
          (bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat) := fun hc₀ => by
    rw [co.out (ctr₂ hc₀), hc, dat₂]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc] at this
    exact this.congr (blockAt_frame ta.frame (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame ta.frame (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame ta.frame (data_taFrame hd₃) (by have := hd₃.lt; omega)]
    exact out₃ hc₀
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₃ : Absorbed s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16)
        (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32) (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) :=
      (hab.congr (blockAt_frame f₂ (stp_saved L (by decide)))
        (bytesAt_frame f₂ (stp_saved L (by omega)) (by omega))).congr
        (blockAt_frame co.frame (stp_crFrame L hd₂ (by decide)))
        (bytesAt_frame co.frame (stp_crFrame L hd₂ (by omega)) (by omega))
    have := ta.abs hab₃
    rw [out₃ hc₀] at this
    exact this
  · rw [hm, blockAt_frame ta.frame (by simpa using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame co.frame (by simpa using stp_crFrame L hd₂ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₂ (by simpa using stp_saved L (d := 0) (k := 16) (by decide))]

theorem dec_run {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' := by
  have L := scLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 7 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (sc1_wp h fun s₁ h1 => ?_)
  have hd₁ := (sc_dataW (k7 := s₀.gpr .r7) h h1.args).ok
  have hH₁ : blockAt s₁.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) :=
    ctxH_keep h1.frame (ctx_saved L)
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L h1.env h1.args spf hin (sc_argsTa h) hH₁ hd₁ ha hP))
    fun s₂ hh => ?_)
  obtain ⟨ta, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨s₃, run₃, h4, h5, h6, hg₃, hK₃⟩ := textArgs_run ta.args spf hin
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := ta.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide)) hK₃.sp hK₃.rd hK₃.wr
  have hk₃ := ta.args.of_eq hK₃.mem hK₃.sp hK₃.rd hK₃.wr
  have ci := sc_crIn h he₃ hk₃ h4 h5 h6 icb hP
  have hd₃ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₄ hh => ?_)
  obtain ⟨co, rd₄, wr₄, sp₄⟩ := hh
  have f₃ : Frame (taFrame (s₀.gpr .r2) (arg s₀ 6) s₀.sp) s₁.mem s₃.mem := by rw [hK₃.mem]; exact ta.frame
  have sv₄ : SavedAt s₄.mem (arg s₀ 6) s₀ :=
    ((h1.saved.frame f₃ (saved_taFrame L))).frame co.frame (saved_crFrame L hd₃)
  refine WP.mono (restore_ok co.env.r11 fW (covers_left co.env.perm.w) sv₄ co.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  have hc : ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (scR s₀) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀) := by
    rw [ciph_keep f₃ (ctx_taFrame L) hR]; exact ciph_keep h1.frame (ctx_saved L) hR
  have ctr₃ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P →
      Ctr s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (scR s₀)) icb P :=
    fun hc₀ => by
      rw [hc]
      exact (hc₀.congr (blockAt_frame h1.frame (stp_saved L (by decide)))
        (blockAt_frame h1.frame (stp_saved L (by decide)))).congr
        (blockAt_frame f₃ (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
        (blockAt_frame f₃ (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  have dat₁ : bytesAt s₁.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat :=
    bytesAt_frame h1.frame (data_saved hd₁) (by have := hd₁.lt; omega)
  have dat₃ : bytesAt s₃.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat := by
    rw [bytesAt_frame f₃ (data_taFrame hd₁) (by have := hd₁.lt; omega), dat₁]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₃ hc₀)
    rwa [hc] at this
  · rw [hm, co.out (ctr₃ hc₀), hc, dat₃]
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₂ := ta.abs ((hab.congr (blockAt_frame h1.frame (stp_saved L (by decide)))
        (bytesAt_frame h1.frame (stp_saved L (by omega)) (by omega))))
    rw [dat₁] at hab₂
    rw [← hK₃.mem] at hab₂
    have hb' := Nat.mod_lt (ghashInput a (ct ++ bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat)).length
      (show 16 > 0 by decide)
    exact hab₂.congr (blockAt_frame co.frame (stp_crFrame L hd₃ (by decide)))
      (bytesAt_frame co.frame (stp_crFrame L hd₃ (by omega)) (by omega))
  · rw [hm, blockAt_frame co.frame (by simpa using stp_crFrame L hd₃ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₃ (by simpa using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame h1.frame (by simpa using stp_saved L (d := 0) (k := 16) (by decide))]

theorem streamEncrypt_wp {s₀ : State} (h : streamEncryptArm.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptArm.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := enc_run h' 0 (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) ciph hh i.1 i.2.1 (gctr ciph (inc32 (j0 hh i.1)) i.2.2) ∧
        arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => enc_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1)
      (ct := gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) i.2.2)
      (low_mod16 hi.2.1).symm (by rw [Proof.Gcm.length_gctr]; exact hi.2.2))
    fun s' hh => ⟨hh.1, fun iv a p hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, p⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [ofNat_lit] at hab hct
  have hl' : (gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamDecrypt_wp {s₀ : State} (h : streamDecryptArm.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptArm.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := dec_run h' 0 (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) ciph hh i.1 i.2.1 i.2.2 ∧
        arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => dec_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1) (ct := i.2.2)
      (low_mod16 hi.2.1).symm hi.2.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [ofNat_lit] at hab hct
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.AesGcm.Arm

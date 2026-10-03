import VerifiedGarbage.Proof.AesGcm.Arm.Seal

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. `open` checks the tag length;
if it is allowed, it computes the tag of the ciphertext into `W + 112`
(`oneAad`, `oneTag 112`), copies the received tag to `W + 256`, compares
the first `tag_len` bytes of each, and decrypts the data in place only if
they are equal; `r0` is the result (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr decryptWith openResult toBytes)
open VG.Proof.Gcm (Absorbed)

theorem SO1.keep {n : Nat} {s₀ s₁ s₂ : State} (h1 : SO1 n s₀ s₁) (hg : ∀ r, r ≠ .r0 → r ≠ .r6 → s₂.gpr r = s₁.gpr r)
    (hk : Keeps s₁ s₂) : SO1 n s₀ s₂ :=
  ⟨h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    by rw [hg _ (by decide) (by decide)]; exact h1.r4, by rw [hg _ (by decide) (by decide)]; exact h1.r5,
    h1.args.of_eq hk.mem hk.sp hk.rd hk.wr, hk.mem ▸ h1.saved, hk.mem ▸ h1.frame⟩

/-- What `open` promises, given the result `r0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt
  | none => s.gpr .r0 = 0 ∧
      bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .r0 = 0)
    (hd : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .r0 = 1)
    (hd : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- The code of `open` once the tag length is known to be allowed. -/
abbrev openGood : Prog isa :=
  .seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 20]) (.seq recv (.seq (cmp uO)
    (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.seq (.ite .eq (.block []) oneCrypt)
      (.block [.mov .r0 (.reg .r7)])))))))

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)
      (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat)
      (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)).take (arg s₀ 5).toNat =
    bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat

/-- After the tags are compared, with the result in `r7` and `Z`. -/
structure OpenMid (s₀ s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s.gpr .r7) (s₀.gpr .r1) s
  args : ArgsKeep 6 s₀ s
  saved : SavedAt s.mem (arg s₀ 4) s₀
  dat : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  ciph : ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  cb : blockAt s.mem (State.addr (oSt s₀) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))
  r7 : s.gpr .r7 = if openTagOk s₀ then 1 else 0
  z : s.z = decide (¬ openTagOk s₀)

/-- `open` up to the comparison of the tags, followed by any `T`. -/
theorem open_head {s₀ s₂ : State} (h : onePre 6 s₀) (h2 : SO1 6 s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = true) {T : Prog isa} {Q : State → Prop}
    (k : ∀ s₈, OpenMid s₀ s₈ → WP isa T s₈ Q) :
    WP isa (.seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 20]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) T)))))) s₂ Q := by
  have L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ 6 ∈ s₀.rd := by rw [h.1]; simp
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (164 ≤ d ∨ d + k ≤ 128) →
      (savedR (arg s₀ 4)).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega) (by decide) h₁
  refine WP.seq (WP.mono (oneAad_ok h (by decide) h2) fun s₃ oa => ?_)
  obtain ⟨k7, he₃⟩ := oa.env
  refine WP.seq (WP.mono (oneTag_ok h (by decide) (o := 112) (.inr rfl) he₃ oa.args oa.hH (length_bytesAt _ _ _).symm
    oa.abs) fun s₄ ot => ?_)
  obtain ⟨k7₄, he₄⟩ := ot.env
  obtain ⟨j5, w5⟩ := ot.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 20] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [j5, w5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, w5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  refine WP.seq (WP.mono (recv_ok L he₅ h6₅ t1 t16) fun s₆ hh => ?_)
  obtain ⟨hb₆, hf₆, g₆, rd₆, wr₆, sp₆⟩ := hh
  have he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₆ rd₆ wr₆
  have h6₆ : s₆.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₅]
  refine WP.seq (WP.mono (cmp_ok L he₆ (o := 112) (.inr rfl) h6₆ t1 t16) fun s₇ hh => ?_)
  obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
  have he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₇ rd₇ wr₇
  -- what the pieces leave
  let rs : List Region := [savedR (arg s₀ 4)] ++ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp ++
    otFrame (oSt s₀) (arg s₀ 4) s₀.sp 112 ++
    [⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 240, 16⟩]
  have F₇ : Frame rs s₀.mem s₇.mem := by
    have e₂ : Frame [savedR (arg s₀ 4)] s₀.mem s₂.mem := h2.frame
    refine ((((e₂.mono ?_).trans (oa.frame.mono ?_)).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [rs, List.mem_append]
    · exact .inl (.inl (.inl hr))
    · exact .inl (.inl (.inr hr))
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have hp := h
  obtain ⟨-, -, dcD, dcW, -, -, -, -, dDW, -, -, bc, -, -, bD, bW, -⟩ := hp
  have dC : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.cs.sub_right (Region.sub_prefix (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
  have dD : ∀ r ∈ rs, (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))
    · exact one_dataJ0 h dDW bD r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [oSt_addr h]; exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact bD.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
  let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  let H := ctxH s₀.mem (State.addr (s₀.gpr .r0))
  let iv := bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat
  let aad := bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat
  let dat := bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  let tl := (arg s₀ 5).toNat
  let tag₀ := bytesAt s₀.mem (State.addr (arg s₀ 4)) tl
  have F₃ : Frame ([savedR (arg s₀ 4)] ++ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp) s₀.mem s₃.mem :=
    (h2.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  have sub₃ : ∀ r ∈ [savedR (arg s₀ 4)] ++ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp, r ∈ rs := fun r hr => by
    simp only [rs, List.mem_append] at hr ⊢; exact .inl (.inl hr)
  have hD₃ : bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = dat :=
    bytesAt_frame F₃ (fun r hr => dD r (sub₃ r hr)) (by omega)
  have hT₄ : bytesAt s₄.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 112) 16 = fullTag ciph H iv aad dat := by
    rw [ot.out, hD₃, ciph_keep F₃ (fun r hr => dC r (sub₃ r hr)) hR, oa.j, ← Proof.Gcm.fullTag_eq]
  have F₄ : Frame ([savedR (arg s₀ 4)] ++ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp ++ otFrame (oSt s₀) (arg s₀ 4) s₀.sp 112)
      s₀.mem s₄.mem :=
    (F₃.mono fun r hr => List.mem_append_left _ hr).trans (ot.frame.mono fun r hr => List.mem_append_right _ hr)
  have hR₀ : bytesAt s₄.mem (State.addr (arg s₀ 4)) tl = tag₀ := by
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega)
    have hst := oSt_addr h
    have z : ∀ {d k : Nat}, d + k ≤ 2560 → 16 ≤ d →
        (⟨State.addr (arg s₀ 4), tl⟩ : Region).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ => by
      have := Lay.w_w (w := arg s₀ 4) (a := 0) (n := tl) (.inl (by omega)) (by omega) h₁
      rwa [add_ofNat_zero] at this
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact z (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact (L.kw.sub_right (Region.sub_prefix (by omega))).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact (L.kw.sub_right (Region.sub_prefix (by omega))).symm
  have hX : (bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 256) 16) ↔ (fullTag ciph H iv aad dat).take tl = tag₀ := by
    rw [hb₆, k₅.mem, hR₀, bytesAt_frame hf₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
        (by omega), k₅.mem, bytesAt_take _ _ t16, hT₄, List.append_cancel_right_eq]
  let X : Prop := bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 256) 16
  obtain ⟨s₈, run₈, h7₈, hz₈, g₈, k₈⟩ : ∃ s₈, runBlock isa [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)] s₇ = some s₈ ∧
      s₈.gpr .r7 = s₇.gpr .r0 ∧ s₈.z = decide ((s₇.gpr .r0).toNat = 0) ∧ (∀ r, r ≠ .r7 → s₈.gpr r = s₇.gpr r) ∧
      Keeps s₇ s₈ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, reduceCtorEq, ite_false]; exact z_sub0 _
    · intro r hr; simp only [gpr_subFlags, gpr_setReg, hr, ite_false]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  have he₈ := he₇.set7 h7₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₈ _ (by decide)) k₈.sp k₈.rd k₈.wr
  have dA6 : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ r ∈ [(⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, 16⟩ : Region)],
      (args s₀ 6).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have hk₈ : ArgsKeep 6 s₀ s₈ :=
    ((((ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr).frame spf hf₆ (dA6 (by decide)) sp₆ rd₆ wr₆).frame spf hf₇
      (dA6 (by decide)) sp₇ rd₇ wr₇).of_eq k₈.mem k₈.sp k₈.rd k₈.wr)
  have F₈ : Frame rs s₀.mem s₈.mem := by rw [k₈.mem]; exact F₇
  have hdat₈ : bytesAt s₈.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = dat := bytesAt_frame F₈ dD (by omega)
  have hc₈ : ciphOf s₈.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat = ciph := ciph_keep F₈ dC hR
  have hcb₈ : blockAt s₈.mem (State.addr (oSt s₀) + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    have F₃₈ : Frame (otFrame (oSt s₀) (arg s₀ 4) s₀.sp 112 ++
        [⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 240, 16⟩])
        s₃.mem s₈.mem := by
      rw [k₈.mem]
      refine ((ot.frame.mono fun r hr => List.mem_append_left _ hr).trans
        ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono fun r hr => ?_)).trans (hf₇.mono fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; simp [hr]
      · simp only [List.mem_singleton] at hr; simp [hr]
    rw [blockAt_frame F₃₈ (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      · have := Lay.st_st (st := oSt s₀) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide)) (by decide)
          (by decide)
        rwa [add_ofNat_zero] at this
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩))]
    exact oa.cb
  have F₂₈ : Frame (j0Frame (oSt s₀) (arg s₀ 4) s₀.sp ++ otFrame (oSt s₀) (arg s₀ 4) s₀.sp 112 ++
      [⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 240, 16⟩])
      s₂.mem s₈.mem := by
    rw [k₈.mem]
    refine (((oa.frame.mono ?_).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [List.mem_append]
    · exact .inl (.inl hr)
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have sv₈ : SavedAt s₈.mem (arg s₀ 4) s₀ := by
    refine h2.saved.frame F₂₈ fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact saved_j0Frame L r hr
    · exact saved_otFrame h (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dW (by decide) (.inl (by decide))
      · exact dW (by decide) (.inl (by decide))
  have hX0 : (s₇.gpr .r0).toNat = 0 ↔ ¬X := by
    rw [h0₇]
    split
    · next hx => exact ⟨fun e => absurd e (by decide), fun e => absurd hx e⟩
    · next hx => exact ⟨fun _ => hx, fun _ => rfl⟩
  refine k s₈ ⟨by rw [h7₈]; exact he₈, hk₈, sv₈, hdat₈, hc₈, hcb₈, ?_, ?_⟩
  · rw [h7₈, h0₇]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  · rw [hz₈]; exact decide_eq_decide.mpr (hX0.trans (not_congr hX))

theorem open_good {s₀ s₂ : State} (h : onePre 6 s₀) (h2 : SO1 6 s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = true) :
    WP isa openGood s₂ fun s => (∃ k7, Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) s) ∧
      SavedAt s.mem (arg s₀ 4) s₀ ∧ OpenPost s₀ s := by
  have L := oneLay h
  refine open_head h h2 hok fun s₈ om => ?_
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite .eq (.block []) oneCrypt) s₈ fun s₉ =>
      Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₈.gpr .r7) (s₀.gpr .r1) s₉ ∧ SavedAt s₉.mem (arg s₀ 4) s₀ ∧
      (openTagOk s₀ → bytesAt s₉.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
        gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
          (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)) ∧
      (¬openTagOk s₀ → bytesAt s₉.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
        bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) := by
    refine WP.ite _ (eval_eq' om.z) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬openTagOk s₀ := of_decide_eq_true ht
      exact WP.block_nil ⟨om.env, om.saved, fun x => absurd x hx, fun _ => om.dat⟩
    · have hx : openTagOk s₀ := Classical.not_not.mp (of_decide_eq_false hf)
      refine WP.mono (oneCrypt_ok h (by decide) om.env om.args om.cb) fun s₉ oc => ?_
      exact ⟨oc.env, om.saved.frame oc.frame (saved_crFrame L (one_dataW h om.args 0 0)),
        fun _ => by rw [oc.out, om.ciph, om.dat], fun x => absurd hx x⟩
  refine WP.seq (WP.mono mid fun s₉ hh => ?_)
  obtain ⟨he₉, sv₉, hd₁, hd₂⟩ := hh
  refine WP.of_runBlock ⟨s₉.setReg .r0 (s₉.gpr .r7), by arun [], ⟨_, he₉.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₉, ?_⟩
  have hres : openRes s₀ = if openTagOk s₀ then
      some (gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
        (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]
  have r0 : (s₉.setReg .r0 (s₉.gpr .r7)).gpr .r0 = if openTagOk s₀ then 1 else 0 := by
    rw [gpr_setReg_self, he₉.r7, om.r7]
  by_cases e : openTagOk s₀
  · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true e)))
      (r0.trans (ite_eq_left_of_eq_true _ _ (eq_true e))) (hd₁ e)
  · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false e)))
      (r0.trans (ite_eq_right_of_eq_false _ _ (eq_false e))) (hd₂ e)

theorem open_wp {s₀ : State} (h : openArm.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  have h' : onePre 6 s₀ := h
  have L := oneLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 6 ∈ s₀.rd := by rw [h'.1]; simp
  refine WP.seq (WP.block_append (one1_wp h' (by decide) fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 20] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine WP.seq (WP.mono (tagLenOk_ok h6₂ (arg s₀ 5).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  have h3 : SO1 6 s₀ s₃ := (h1.keep (fun r a b => g₂ r b) k₂).keep (fun r a b => g₃ r a) k₃
  have mid : WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) openGood) s₃ fun s =>
      (∃ k7, Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) s) ∧
      SavedAt s.mem (arg s₀ 4) s₀ ∧ OpenPost s₀ s := by
    refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => open_good h' h3 (by simpa using hf))
    have hbad : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = false := by simpa using ht
    refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, h3.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, h3.saved, ?_⟩
    refine openPost_none (by simp only [openRes, openResult, hbad]; rfl) (by simp [gpr_setReg]) ?_
    show bytesAt s₃.mem _ _ = _
    exact bytesAt_frame h3.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h'.2.2.2.2.2.2.2.2.1.sub_right (Lay.wSub (by decide))) (by omega)
  refine WP.seq (WP.mono mid fun s₄ hh => ?_)
  obtain ⟨⟨k7, he⟩, sv, op⟩ := hh
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, ?_⟩
  have e : OpenPost s₀ s' := by
    unfold OpenPost at op ⊢; rw [hh.2.1, hh.2.2.1]; exact op
  exact e

end VG.Proof.AesGcm.Arm

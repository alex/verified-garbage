import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
import VerifiedGarbage.Proof.AesGcm.Arm.Compare

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. `stream_verify` saves our
caller's registers in `work` (`W`), checks the tag length, and, if it is
allowed, copies the received tag to `W + 256`, writes the tag to `W`, compares
the first `tag_len` bytes of each and masks the tag with the result; if the
length is not allowed it zeroes the tag (`streamVerify_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag zeros)
open VG.Proof.Cmac (store4)

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : bytesAt m p k = (bytesAt m p n).take k := by
  rw [show n = k + (n - k) by omega, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem tagLenOk_bounds {tl : Nat} (h : Spec.Gcm.tagLenOk tl = true) : 1 ≤ tl ∧ tl ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → arg64 s₀ 0 = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct
    if Spec.Gcm.tagLenOk (arg s₀ 5).toNat ∧ t.take (arg s₀ 5).toNat = bytesAt s₀.mem (State.addr (arg s₀ 4))
        (arg s₀ 5).toNat then
      s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (arg s₀ 4)) 16 = t
    else s.gpr .r0 = 0 ∧ bytesAt s.mem (State.addr (arg s₀ 4)) 16 = zeros 16

theorem ver_run {s₀ : State} (h : finPre 6 s₀) {a ct : List Byte} (ha : a.length % 16 = (arg s₀ 0).toNat % 16)
    (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VerPost s₀ a ct s' := by
  have L := finLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 6 ∈ s₀.rd := by rw [h.1]; simp
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (164 ≤ d ∨ d + k ≤ 128) →
      (savedR (arg s₀ 4)).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega) (by decide) h₁
  refine WP.seq (WP.block_append (fin1_wp h (by decide) fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 20] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) k₂.sp k₂.rd k₂.wr
  refine WP.seq (WP.mono (tagLenOk_ok h6₂ (arg s₀ 5).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  have k₁₃ := k₂.trans k₃
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  have hk₃ := h1.args.of_eq k₁₃.mem k₁₃.sp k₁₃.rd k₁₃.wr
  have sv₃ : SavedAt s₃.mem (arg s₀ 4) s₀ := k₁₃.mem ▸ h1.saved
  have mid : WP isa (.ite .eq (.block (zero16 0)) (.seq recv (.seq (finTag 0) (.seq (.block [.ldrSp .r6 20])
      (.seq (cmp 0) (.block mask)))))) s₃ fun s' => (∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp k7
        (s₀.gpr .r1) s') ∧ SavedAt s'.mem (arg s₀ 4) s₀ ∧ VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = false := by simpa using ht
      obtain ⟨s₄, run₄, hm₄, g₄, rd₄, wr₄, sp₄, h0₄⟩ := zero16_ok L he₃ (d := 0) (by decide) (by decide)
      refine WP.of_runBlock ⟨s₄, run₄, ⟨_, he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide)) sp₄ rd₄ wr₄⟩, ?_, fun iv _ _ => ?_⟩
      · exact sv₃.frame (by rw [hm₄]; exact Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dW (by decide) (.inr (by decide)))
      · simp only [hbad, Bool.false_eq_true, false_and, ite_false]
        refine ⟨h0₄, ?_⟩
        rw [hm₄, add_ofNat_zero]; exact store4_zero_bytes _ _
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = true := by simpa using hf
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      have h6₃ : s₃.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat := by rw [g₃ _ (by decide), h6₂]
      refine WP.seq (WP.mono (recv_ok L he₃ h6₃ t1 t16) fun s₄ hh => ?_)
      obtain ⟨hb₄, hf₄, g₄, rd₄, wr₄, sp₄⟩ := hh
      have he₄ := he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₄ rd₄ wr₄
      have dA : ∀ {d k : Nat}, d + k ≤ 2560 → (args s₀ 6).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      have hk₄ := hk₃.frame spf hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dA (by decide)) sp₄ rd₄ wr₄
      have f₀₄ : Frame [savedR (arg s₀ 4), ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
        (h1.frame.mono (by simp)).trans ((k₁₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
      have dc₀₄ : ∀ r ∈ [savedR (arg s₀ 4), ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
      have ds₀₄ : ∀ r ∈ [savedR (arg s₀ 4), ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r2), 80⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 80) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
      refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (na := 6) (by decide) (o := 0) (.inl rfl) he₄ hk₄ spf hin
        (fin_argsTag h (.inl rfl)) (show s₀.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat by simp) hR
        (ctxH_keep f₀₄ dc₀₄) ha hP)) fun s₅ hh => ?_)
      obtain ⟨fo, rd₅, wr₅, sp₅⟩ := hh
      obtain ⟨k7₅, he₅⟩ := fo.env
      obtain ⟨j5, w5⟩ := fo.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
      obtain ⟨s₆, run₆, h6₆, g₆, k₆⟩ : ∃ s₆, runBlock isa [.ldrSp .r6 20] s₅ = some s₆ ∧
          s₆.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r) ∧ Keeps s₅ s₆ := by
        refine ⟨_, by arun [j5, w5], ?_, ?_, ?_⟩
        · simp [gpr_setReg, w5]
        · intro r hr; simp [gpr_setReg, hr]
        · exact ⟨rfl, rfl, rfl, rfl⟩
      refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
      have he₆ := he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) k₆.sp k₆.rd k₆.wr
      refine WP.seq (WP.mono (cmp_ok L he₆ (o := 0) (.inl rfl) h6₆ t1 t16) fun s₇ hh => ?_)
      obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
      have he₇ := he₆.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₇ rd₇ wr₇
      obtain ⟨s₈, run₈, hb₈, hf₈, g₈, rd₈, wr₈, sp₈⟩ := mask_ok L he₇
        (b := decide (bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 0) (arg s₀ 5).toNat ++
          zeros (16 - (arg s₀ 5).toNat) = bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 256) 16))
        (by rw [h0₇]; simp only [decide_eq_true_eq])
      refine WP.of_runBlock ⟨s₈, run₈, ⟨k7₅, he₇.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₈ _ (by decide) (by decide)) sp₈ rd₈ wr₈⟩, ?_,
        fun iv hs hl => ?_⟩
      · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dW (by decide) (.inl (by decide)))).frame fo.frame
          (saved_tagFrame L (.inl rfl))
        have sv₆ : SavedAt s₆.mem (arg s₀ 4) s₀ := k₆.mem ▸ sv₅
        refine (sv₆.frame hf₇ ?_).frame hf₈ ?_
        all_goals intro r hr; simp only [List.mem_singleton] at hr; subst hr
        · exact dW (by decide) (.inl (by decide))
        · simpa using dW (d := 0) (k := 16) (by decide) (.inr (by decide))
      · have ht' : bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 0) 16 =
            fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := by
          rw [k₆.mem]; exact fin_out h f₀₄ dc₀₄ ds₀₄ fo hs hl
        have hrc : bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 256) 16 =
            bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat ++ zeros (16 - (arg s₀ 5).toNat) := by
          rw [k₆.mem, bytesAt_frame fo.frame (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl | rfl
              · have := L.st_w (a := 0) (n := 32) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
                simp only [add_ofNat_zero] at this
                exact this.symm
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
              · exact (L.stk_w (by decide)).symm) (by decide), hb₄, k₁₃.mem,
            bytesAt_frame h1.frame (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              simpa using (dW (d := 0) (k := (arg s₀ 5).toNat) (by omega) (.inr (by omega))).symm) (by omega)]
        have hX : (bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 0) (arg s₀ 5).toNat ++
              zeros (16 - (arg s₀ 5).toNat) = bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 256) 16) ↔
            (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (arg s₀ 5).toNat =
              bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat := by
          rw [bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
        have hW₇ : bytesAt s₇.mem (State.addr (arg s₀ 4)) 16 = bytesAt s₆.mem (State.addr (arg s₀ 4)) 16 :=
          bytesAt_frame hf₇ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            simpa using Lay.w_w (w := arg s₀ 4) (a := 0) (n := 16) (d := 240) (k := 16) (.inl (by decide)) (by decide)
              (by decide)) (by decide)
        have hr0 : s₈.gpr .r0 = s₇.gpr .r0 := g₈ _ (by decide) (by decide)
        simp only [hok, true_and]
        by_cases e : (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (arg s₀ 5).toNat =
              bytesAt s₀.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat
        · have e' := hX.mpr e
          simp only [e, ite_true]
          refine ⟨by rw [hr0, h0₇]; simp only [e', ite_true], ?_⟩
          rw [hb₈, decide_eq_true e']; simp only [ite_true]; rw [hW₇, ← ht', add_ofNat_zero]
        · have e' : ¬ _ := fun x => e (hX.mp x)
          simp only [e, ite_false]
          refine ⟨by rw [hr0, h0₇]; simp only [e', ite_false], ?_⟩
          rw [hb₈, decide_eq_false e']; rfl

  refine WP.seq (WP.mono mid fun s₄ hh => ?_)
  obtain ⟨⟨k7, he⟩, sv, vp⟩ := hh
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [hh.2.1, hh.2.2.1]; exact this

theorem streamVerify_wp {s₀ : State} (h : streamVerifyArm.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyArm.post s₀ s' := by
  have h' : finPre 6 s₀ := h
  have h₀ := ver_run h' (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      arg64 s₀ 0 = BitVec.ofNat 64 i.1.length ∧ (arg64 s₀ 2).toNat = i.2.length)
    fun i hi => WP.mono (ver_run h' (a := i.1) (ct := i.2) (low_mod16 hi.1).symm hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl⟩

end VG.Proof.AesGcm.Arm

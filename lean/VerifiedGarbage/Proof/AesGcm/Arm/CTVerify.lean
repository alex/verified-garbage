import VerifiedGarbage.Proof.AesGcm.Arm.CTFin

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. Only the (public) tag length
decides which code runs: the tags are compared and the result applied
without a branch.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

/-- `rel_ite`, with a postcondition. -/
theorem rel_iteQ {F F' : State → Prop} {Q : State → State → Prop} {t e : Prog isa} (b : Bool)
    (hz : ∀ s, F s → s.z = b) (hz' : ∀ s, F' s → s.z = b)
    (ht : b = true → RelCT isa (fun a b => F a ∧ F' b) t Q)
    (he : b = false → RelCT isa (fun a b => F a ∧ F' b) e Q) :
    RelCT isa (fun a b => F a ∧ F' b) (.ite .eq t e) Q := by
  refine RelCT.ite (fun _ _ h => by rw [eval_eq' (hz _ h.1), eval_eq' (hz' _ h.2)]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

/-- `finTag`'s state with the tag length in `r6`. -/
def P6 (c st w sp : BitVec 32) (R tl : Nat) (t₀ s : State) : Prop :=
  FT 6 t₀ c st w sp R s ∧ s.gpr .r6 = BitVec.ofNat 32 tl

/-- After the comparison: `r0` is 1 or 0. -/
def P7 (c st w sp : BitVec 32) (R : Nat) (t₀ s : State) : Prop :=
  FT 6 t₀ c st w sp R s ∧ ∃ b : Bool, s.gpr .r0 = if b then 1 else 0

theorem ite_bool {p : Prop} [Decidable p] {x : BitVec 32} (h : x = if p then 1 else 0) :
    ∃ b : Bool, x = if b then 1 else 0 :=
  ⟨decide p, by rw [h]; simp only [decide_eq_true_eq]⟩

section
variable {c st w sp : BitVec 32} {R tl : Nat} {t₀ : State}

theorem ld6_wp {s : State} (hf : t₀.sp.toNat + 4 * 6 ≤ 2 ^ 32) (hin : args t₀ 6 ∈ t₀.rd)
    (h5 : (arg t₀ 5).toNat = tl) (h : FT 6 t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 20]) s (P6 c st w sp R tl t₀) := by
  subst h5
  obtain ⟨k7, he, hk⟩ := h
  obtain ⟨i5, v5⟩ := hk.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp [gpr_setReg, v5]

theorem tlo_wp {s : State} (htl : tl < 2 ^ 32) (h : P6 c st w sp R tl t₀ s) :
    WP isa tagLenOk s fun s' => P6 c st w sp R tl t₀ s' ∧ s'.z = !Spec.Gcm.tagLenOk tl := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (tagLenOk_ok h6 htl) fun s' ⟨hz, g, k⟩ => ⟨⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, by rw [g _ (by decide), h6]⟩, hz⟩

variable (L : Lay c st w sp)
include L

theorem zero_wp {s : State} (h : FT 6 t₀ c st w sp R s) :
    WP isa (.block (zero16 0)) s fun s' => s'.gpr .r11 = w := by
  obtain ⟨k7, he, -⟩ := h
  obtain ⟨s₄, run₄, -, g₄, -⟩ := zero16_ok L he (d := 0) (by decide) (by decide)
  exact WP.of_runBlock ⟨s₄, run₄, by rw [g₄ _ (by decide), he.r11]⟩

theorem recv_wp {s : State} (hf : t₀.sp.toNat + 4 * 6 ≤ 2 ^ 32)
    (hD : (args t₀ 6).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (h : P6 c st w sp R tl t₀ s) : WP isa recv s (P6 c st w sp R tl t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (recv_ok L he h6 h1 h16) fun s' ⟨_, hf₄, g₄, rd₄, wr₄, sp₄⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₄ rd₄ wr₄,
    hk.frame hf hf₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₄ rd₄ wr₄⟩, ?_⟩
  rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]

theorem ft_wp {s : State} (hf : t₀.sp.toNat + 4 * 6 ≤ 2 ^ 32) (hin : args t₀ 6 ∈ t₀.rd)
    (hA : ∀ r ∈ tagFrame st w sp 0, (args t₀ 6).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h : FT 6 t₀ c st w sp R s) : WP isa (finTag 0) s (FT 6 t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := h
  exact WP.mono (finTag_ok L (by decide) (.inl rfl) he hk hf hin hA rfl hR rfl
    (a := List.replicate ((arg t₀ 0).toNat % 16) 0) (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0)
    (by simp) (by simp)) fun s' h => ⟨h.env.choose, h.env.choose_spec, h.args⟩

theorem cmp_wp {s : State} (hf : t₀.sp.toNat + 4 * 6 ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hD : (args t₀ 6).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (h : P6 c st w sp R tl t₀ s) : WP isa (cmp o) s (P7 c st w sp R t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (cmp_ok L he ho h6 h1 h16) fun s' ⟨h0, hf₇, g₇, rd₇, wr₇, sp₇⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₇ rd₇ wr₇,
    hk.frame hf hf₇ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₇ rd₇ wr₇⟩,
    ite_bool h0⟩

theorem mask_wp {s : State} (h : P7 c st w sp R t₀ s) : WP isa (.block mask) s fun s' => s'.gpr .r11 = w := by
  obtain ⟨⟨k7, he, -⟩, b, h0⟩ := h
  obtain ⟨s', run, -, -, g, -⟩ := mask_ok L he h0
  exact WP.of_runBlock ⟨s', run, by rw [g _ (by decide) (by decide), he.r11]⟩

end

theorem streamVerify_rel {s₀ s₀' : State} (h0 : streamVerifyArm.pre s₀) (h0' : streamVerifyArm.pre s₀')
    (hq : streamVerifyArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamVerify fun _ _ => True := by
  have h0₆ : finPre 6 s₀ := h0
  have h0₆' : finPre 6 s₀' := h0'
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := id hq
  have L := finLay h0₆
  have hR := h0₆.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h0₆.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0₆'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 6 ∈ s₀.rd := by rw [h0₆.1]; simp
  have hin' : args s₀' 6 ∈ s₀'.rd := by rw [h0₆'.1]; simp
  have hA := fin_argsTag h0₆ (o := 0) (.inl rfl)
  have hA' : ∀ r ∈ tagFrame (s₀.gpr .r2) (arg s₀ 4) s₀.sp 0, (args s₀' 6).Disjoint r := by
    have := fin_argsTag h0₆' (o := 0) (.inl rfl); rwa [← q₃, ← qa 4 (by decide), ← q₀] at this
  have hD : ∀ {d k : Nat}, d + k ≤ 2560 →
      (args s₀ 6).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
    fun hd => (h0₆.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have hD' : ∀ {d k : Nat}, d + k ≤ 2560 →
      (args s₀' 6).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ := fun hd => by
    rw [qa 4 (by decide)]; exact (h0₆'.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have h5' : (arg s₀' 5).toNat = (arg s₀ 5).toNat := by rw [qa 5 (by decide)]
  have e1 : BitVec.ofNat 32 (s₀.gpr .r1).toNat = s₀.gpr .r1 := by simp
  -- shorthands for the public data
  let P6₀ := P6 (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat
  let FT₀ := fun t₀ => FT 6 t₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat
  let P7₀ := P7 (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat
  let P3 : State → State → Prop := fun t₀ s => P6₀ t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (arg s₀ 5).toNat
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 4
  have r11 : ∀ {t₀ s}, FT₀ t₀ s → s.gpr .r11 = arg s₀ 4 := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
    (argTaint [.r0, .r1, .r2] (4 * 6)) (c := .block (finEntry ++ [.ldrSp .r6 20])) (fin_entry_agree h0₆ h0₆' hq)
    ⟨_, by taint_decide⟩
    (fun s e => by
      rw [e]
      exact WP.block_append (fin1_wp h0₆ (by decide) fun s₁ h1 =>
        ld6_wp spf hin rfl ⟨_, by rw [e1]; exact h1.env, h1.args⟩))
    (fun s e => by
      rw [e]
      exact WP.block_append (fin1_wp h0₆' (by decide) fun s₁ h1 =>
        ld6_wp spf' hin' h5' ⟨_, by
          have := h1.env; rw [← q₁, ← q₂, ← q₃, ← qa 4 (by decide), ← q₀] at this; rw [e1]; exact this, h1.args⟩))
  -- whether the length is allowed
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  have b := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := P3 s₀) (G' := P3 s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tlo_wp (arg s₀ 5).isLt h) (fun s h => tlo_wp (arg s₀ 5).isLt h)
  -- the branches
  have mid : RelCT isa (fun a b => P3 s₀ a ∧ P3 s₀' b)
      (.ite .eq (.block (zero16 0)) (.seq recv (.seq (finTag 0) (.seq (.block [.ldrSp .r6 20])
        (.seq (cmp 0) (.block mask)))))) fun a b => W a ∧ W b := by
    refine rel_iteQ (!Spec.Gcm.tagLenOk (arg s₀ 5).toNat) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block (zero16 0)) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := P3 s₀) (F' := P3 s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [r11 h.1.1.1, r11 h.2.1.1]) hc)
        (fun s h => zero_wp L h.1.1) (fun s h => zero_wp L h.1.1)
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = true := by simpa using hb
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      obtain ⟨_, c1⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) recv h).isSome = true := ⟨_, by taint_decide⟩
      have x1 := rel_wp (F := P3 s₀) (F' := P3 s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.1.2, h.2.1.2]
          · rw [r11 h.1.1.1, r11 h.2.1.1]) c1)
        (fun s h => recv_wp L spf (hD (by decide)) t1 t16 h.1) (fun s h => recv_wp L spf' (hD' (by decide)) t1 t16 h.1)
      have x2 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := FT₀ s₀) (G' := FT₀ s₀')
        (finTag_rel L (na := 6) (by decide) (o := 0) (.inl rfl) hR spf q₀ qa (fin_hw h0₆) (fin_hw h0₆') hin hin'
          hA hA' |>.mono (fun s s' h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
        (fun s h => ft_wp L spf hin hA hR h.1) (fun s h => ft_wp L spf' hin' hA' hR h.1)
      have x3 := rel_agree (F := FT₀ s₀) (F' := FT₀ s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (argTaint [] (4 * 6)) (c := .block [.ldrSp .r6 20])
        (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (fin_hw h0₆) (fin_hw h0₆') (rs := [])
          (by simp)) ⟨_, by taint_decide⟩
        (fun s h => ld6_wp spf hin rfl h) (fun s h => ld6_wp spf' hin' h5' h)
      obtain ⟨_, c4⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp 0) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have x4 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := P7₀ s₀) (G' := P7₀ s₀')
        (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.2, h.2.2]
          · rw [r11 h.1.1, r11 h.2.1]) c4)
        (fun s h => cmp_wp L spf (.inl rfl) (hD (by decide)) t1 t16 h)
        (fun s h => cmp_wp L spf' (.inl rfl) (hD' (by decide)) t1 t16 h)
      obtain ⟨_, c5⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block mask) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have x5 := rel_wp (F := P7₀ s₀) (F' := P7₀ s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [r11 h.1.1, r11 h.2.1]) c5)
        (fun s h => mask_wp L h) (fun s h => mask_wp L h)
      exact x1.seq (x2.seq (x3.seq (x4.seq x5)))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) hB
  exact a.seq (b.seq (mid.seq d))

theorem streamVerify_ct : ConstantTime isa streamVerifyArm.pre streamVerifyArm.pub streamVerify :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamVerify_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

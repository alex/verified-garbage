import VerifiedGarbage.Proof.AesGcm.Arm.CTText

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

theorem sc_pubs {s₀ s₀' : State} (hq : streamCryptPub s₀ s₀') : s₀.sp = s₀'.sp ∧ s₀.gpr .r0 = s₀'.gpr .r0 ∧
    s₀.gpr .r1 = s₀'.gpr .r1 ∧ s₀.gpr .r2 = s₀'.gpr .r2 ∧ ∀ i < 7, arg s₀ i = arg s₀' i := hq

/-- The stack arguments are apart from the writable regions. -/
theorem sc_hw {t : State} (ht : streamCryptPre t) : ∀ r ∈ t.wr, (args t 7).Disjoint r := by
  obtain ⟨-, hwr, -, -, -, -, -, dsA, -, dDA, dWA, -⟩ := ht
  intro r hr
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dsA.symm
  · exact dDA.symm
  · exact dWA.symm

/-- After the entry of `encrypt` (or the arguments of `crypt`). -/
def EC1 (s₀ : State) (s : State) : Prop :=
  ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s ∧ ArgsKeep 7 s₀ s ∧
    s.gpr .r4 = arg s₀ 4 ∧ s.gpr .r5 = arg s₀ 5 ∧ s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16)

/-- Two runs' pieces agree on everything public. -/
theorem ec1_crI {s₀ s : State} (h : streamCryptPre s₀) (he : EC1 s₀ s) :
    CrI (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp (s₀.gpr .r1) (s₀.gpr .r1).toNat (arg s₀ 4) (arg s₀ 5).toNat
      ((arg s₀ 2).toNat % 16) s := by
  obtain ⟨k7, he, hk, h4, h5, h6⟩ := he
  exact ⟨k7, 0, (arg s₀ 3 ++ arg s₀ 2).toNat, (lowTo_mod16 rfl).symm, sc_crIn h he hk h4 h5 h6 0 rfl⟩

theorem ec1_crypt {s₀ s : State} (h : streamCryptPre s₀) (he : EC1 s₀ s) :
    WP isa crypt s (fun s' => TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s' ∧
      ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s') := by
  have L := scLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨k7, icb, P, -, ci⟩ := ec1_crI h he
  obtain ⟨_, _, hk, _⟩ := he
  refine WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s' ⟨co, rd, wr, sp⟩ => ?_
  have hk' := hk.frame spf co.frame (sc_argsCr h) sp rd wr
  exact ⟨⟨_, _, co.env, hk', (sc_dataW (k7 := k7) h hk').ok⟩, _, co.env⟩

theorem streamEncrypt_rel {s₀ s₀' : State} (h0 : streamCryptPre s₀) (h0' : streamCryptPre s₀')
    (hq : streamCryptPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamEncrypt fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := sc_pubs hq
  have L := scLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : ∀ {t : State}, streamCryptPre t → args t 7 ∈ t.rd := fun {t} ht => by rw [ht.1]; simp
  have e1 : ∀ {t : State}, streamCryptPre t → WP isa (.block (cryptEntry ++ textArgs)) t (EC1 t) := fun {t} ht => by
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine WP.block_append (sc1_wp ht fun s₁ h1 => ?_)
    obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := textArgs_run h1.args spf (hin ht)
    exact WP.of_runBlock ⟨s', run, _, h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
      h1.args.of_eq hK.mem hK.sp hK.rd hK.wr, h4, h5, h6⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := EC1 s₀) (G' := EC1 s₀')
    (argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block (cryptEntry ++ textArgs))
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 7 s).agree (ArgsKeep.refl 7 s') q₀ spf qa (sc_hw h0) (sc_hw h0')
        fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact e1 h0) (fun s e => by rw [e]; exact e1 h0')
  let G₂ : State → Prop := fun s => TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s
  let G₂' : State → Prop := fun s => TA s₀' (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s
  have b := rel_wp (F := EC1 s₀) (F' := EC1 s₀') (G := G₂) (G' := G₂')
    (rel_of_ct (crypt_ct L) (fun s he => ec1_crI h0 he) (fun s he => by
      have := ec1_crI h0' he
      rwa [← q₁, ← q₂, ← q₃, ← q₀, ← qa 2 (by decide), ← qa 4 (by decide), ← qa 5 (by decide),
        ← qa 6 (by decide)] at this))
    (fun s he => WP.mono (ec1_crypt h0 he) fun _ h => h.1)
    (fun s he => WP.mono (ec1_crypt h0' he) fun _ h => by
      have := h.1; rwa [← q₁, ← q₃, ← q₀, ← qa 6 (by decide)] at this)
  have c := textAbsorb_rel L spf q₀ qa (sc_hw h0) (sc_hw h0') (hin h0) (hin h0')
    (sc_argsTa h0) (by
      have := sc_argsTa h0'; rwa [← q₃, ← qa 6 (by decide), ← q₀] at this)
  let G₃ : State → Prop := fun s => ∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 k8 s
  have ta : ∀ {t₀ : State}, streamCryptPre t₀ → t₀.sp = s₀.sp → arg t₀ 6 = arg s₀ 6 →
      t₀.gpr .r0 = s₀.gpr .r0 → t₀.gpr .r2 = s₀.gpr .r2 → ∀ s, TA t₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s →
      WP isa textAbsorb s G₃ := fun {t₀} ht e0 e6 er0 er2 s ⟨k7, k8, he, hk, hd⟩ => by
    have Lt := scLay ht
    rw [e0, e6, er0, er2] at Lt
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hA := sc_argsTa ht
    rw [e0, e6, er2] at hA
    exact WP.mono (textAbsorb_ok Lt (a := List.replicate ((arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0) he hk spf (hin ht) hA rfl hd (by simp) (by simp))
      fun s' h => ⟨_, _, h.env⟩
  have d := rel_wp (F := G₂) (F' := G₂') (G := G₃) (G' := G₃) c
    (ta h0 rfl rfl rfl rfl) (ta h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₃.symm)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) (P := fun s₁ s₂ => G₃ s₁ ∧ G₃ s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hB
  exact a.seq (b.seq (d.seq e))

theorem streamDecrypt_rel {s₀ s₀' : State} (h0 : streamCryptPre s₀) (h0' : streamCryptPre s₀')
    (hq : streamCryptPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamDecrypt fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := sc_pubs hq
  have L := scLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : ∀ {t : State}, streamCryptPre t → args t 7 ∈ t.rd := fun {t} ht => by rw [ht.1]; simp
  let G₁ : State → Prop := fun s => TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
    ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s
  let G₁' : State → Prop := fun s => TA s₀' (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
    ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s
  have e1 : ∀ {t : State}, streamCryptPre t → t.sp = s₀.sp → arg t 6 = arg s₀ 6 → t.gpr .r0 = s₀.gpr .r0 →
      t.gpr .r1 = s₀.gpr .r1 → t.gpr .r2 = s₀.gpr .r2 →
      WP isa (.block cryptEntry) t fun s => TA t (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
        ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s :=
    fun {t} ht e0 e6 er0 er1 er2 => sc1_wp ht fun s₁ h1 => by
      have he := h1.env
      rw [e0, e6, er0, er1, er2] at he
      have hd := (sc_dataW (k7 := t.gpr .r7) ht h1.args).ok
      rw [e0, e6, er2] at hd
      exact ⟨⟨_, _, he, h1.args, hd⟩, _, he⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G₁) (G' := G₁')
    (argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block cryptEntry)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 7 s).agree (ArgsKeep.refl 7 s') q₀ spf qa (sc_hw h0) (sc_hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact e1 h0 rfl rfl rfl rfl rfl)
    (fun s e => by rw [e]; exact e1 h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₂.symm q₃.symm)
  have c := textAbsorb_rel L spf q₀ qa (sc_hw h0) (sc_hw h0') (hin h0) (hin h0')
    (sc_argsTa h0) (by
      have := sc_argsTa h0'; rwa [← q₃, ← qa 6 (by decide), ← q₀] at this)
  let G₂ : State → State → Prop := fun t₀ s =>
    ∃ k7, Env (t₀.gpr .r0) (t₀.gpr .r2) (arg t₀ 6) t₀.sp k7 (t₀.gpr .r1) s ∧ ArgsKeep 7 t₀ s
  have ta : ∀ {t₀ : State}, streamCryptPre t₀ → t₀.sp = s₀.sp → arg t₀ 6 = arg s₀ 6 →
      t₀.gpr .r0 = s₀.gpr .r0 → t₀.gpr .r1 = s₀.gpr .r1 → t₀.gpr .r2 = s₀.gpr .r2 → ∀ s,
      (TA t₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
        ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s) →
      WP isa textAbsorb s (G₂ t₀) := fun {t₀} ht e0 e6 er0 er1 er2 s ⟨⟨_, _, _, hk, hd⟩, k7, he⟩ => by
    have Lt := scLay ht
    rw [e0, e6, er0, er2] at Lt
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hA := sc_argsTa ht
    rw [e0, e6, er2] at hA
    refine WP.mono (textAbsorb_ok Lt (a := List.replicate ((arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0) he hk spf (hin ht) hA rfl hd (by simp) (by simp))
      fun s' h => ⟨k7, ?_, h.args⟩
    have := h.env
    rwa [← e0, ← e6, ← er0, ← er1, ← er2] at this
  have d := rel_wp (F := G₁) (F' := G₁') (G := G₂ s₀) (G' := G₂ s₀') (c.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
    fun _ _ h => h) (ta h0 rfl rfl rfl rfl rfl) (ta h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₂.symm q₃.symm)
  -- the arguments of `crypt`
  have e3 : ∀ {t₀ : State}, streamCryptPre t₀ → ∀ s, G₂ t₀ s → WP isa (.block textArgs) s (EC1 t₀) :=
    fun {t₀} ht s ⟨k7, he, hk⟩ => by
      have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := textArgs_run hk spf (hin ht)
      exact WP.of_runBlock ⟨s', run, _, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
        hk.of_eq hK.mem hK.sp hK.rd hK.wr, h4, h5, h6⟩
  have f := rel_agree (F := G₂ s₀) (F' := G₂ s₀') (argTaint [] (4 * 7)) (c := .block textArgs)
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => k.agree k' q₀ spf qa (sc_hw h0) (sc_hw h0') (by simp)) ⟨_, by taint_decide⟩
    (e3 h0) (e3 h0')
  let G₃ : State → Prop := fun s => ∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 k8 s
  have g := rel_wp (F := EC1 s₀) (F' := EC1 s₀') (G := G₃) (G' := G₃)
    (rel_of_ct (crypt_ct L) (fun s he => ec1_crI h0 he) (fun s he => by
      have := ec1_crI h0' he
      rwa [← q₁, ← q₂, ← q₃, ← q₀, ← qa 2 (by decide), ← qa 4 (by decide), ← qa 5 (by decide),
        ← qa 6 (by decide)] at this))
    (fun s he => WP.mono (ec1_crypt h0 he) fun _ h => h.2.elim fun k7 he => ⟨k7, _, he⟩)
    (fun s he => WP.mono (ec1_crypt h0' he) fun _ h => h.2.elim fun k7 he => by
      rw [← q₁, ← q₃, ← q₀, ← qa 6 (by decide)] at he; exact ⟨k7, _, he⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) (P := fun s₁ s₂ => G₃ s₁ ∧ G₃ s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hB
  exact a.seq (d.seq (f.seq (g.seq e)))

theorem streamEncrypt_ct : ConstantTime isa streamEncryptArm.pre streamEncryptArm.pub streamEncrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamEncrypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem streamDecrypt_ct : ConstantTime isa streamDecryptArm.pre streamDecryptArm.pub streamDecrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamDecrypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

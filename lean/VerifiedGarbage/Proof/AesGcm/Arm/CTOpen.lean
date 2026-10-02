import VerifiedGarbage.Proof.AesGcm.Arm.CTOne
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_seal` and `vg_aes_gcm_open` are constant time

Untrusted: everything here is checked by Lean. `open` decrypts only if the
tags are equal, which its contract makes public: the comparison, done
without a branch, is related across the runs by what each run computes
(`rel_ghost`, `open_head`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

theorem one_entry_agree {n : Nat} {rs : List Reg} (hrs : ∀ r ∈ rs, r = .r0 ∨ r = .r1 ∨ r = .r2 ∨ r = .r3)
    {s₀ s₀' : State} (h0 : onePre n s₀) (h0' : onePre n s₀') (hq : onePub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (argTaint rs (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 qa (one_hw h0) (one_hw h0') fun r hr => ?_
  rcases hrs r hr with rfl | rfl | rfl | rfl <;> assumption

theorem seal_rel {s₀ s₀' : State} (h0 : sealArm.pre s₀) (h0' : sealArm.pre s₀') (hq : sealArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «seal» fun _ _ => True := by
  have h5 : onePre 5 s₀ := h0
  have h5' : onePre 5 s₀' := h0'
  have hq5 : onePub 5 s₀ s₀' := hq
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SO1 5 s₀) (G' := SO1 5 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 5)) (c := .block oneEntry)
    (one_entry_agree (by simp) h5 h5' hq5) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact one1_wp h5 (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact one1_wp h5' (by decide) fun _ h => h)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => OF 5 s₀ s₀ s₁ ∧ OF 5 s₀ s₀' s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.choose_spec.1.r11, h.2.choose_spec.1.r11]) hB
  exact a.seq ((oneAad_rel h5 h5' hq5 (by decide)).seq ((oneCrypt_rel h5 h5' hq5 (by decide)).seq
    ((oneTag_rel h5 h5' hq5 (by decide) (.inl rfl)).seq d)))

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `open` -/

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (arg t 5).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  have e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Gcm.ctxCiph t.mem (State.addr (t.gpr .r0)) (t.gpr .r1).toNat)
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (State.addr (t.gpr .r0)))
          (Spec.Aes.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat)))
        (Spec.Aes.bytesAt t.mem (State.addr (arg t 2)) (arg t 3).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), decide_eq_true h]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), decide_eq_false h]; rfl

theorem open1_wp {t₀ : State} (h : onePre 6 t₀) :
    WP isa (.block (oneEntry ++ [.ldrSp .r6 20])) t₀ fun s =>
      SO1 6 t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg t₀ 5).toNat := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args t₀ 6 ∈ t₀.rd := by rw [h.1]; simp
  refine WP.block_append (one1_wp h (by decide) fun s₁ h1 => ?_)
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
  exact ⟨h1.keep (fun r _ b => by simp [gpr_setReg, b]) ⟨rfl, rfl, rfl, rfl⟩, by simp [gpr_setReg, v5]⟩

section
variable {c st w sp : BitVec 32} {R : Nat} {t₀ : State}

theorem blk_wp {s : State} (h : P7 c st w sp R t₀ s) :
    WP isa (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) s (FT 6 t₀ c st w sp R) := by
  obtain ⟨⟨k7, he, hk⟩, -⟩ := h
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  exact ⟨_, he.set7 rfl (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_subFlags, gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem mov07_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (.reg .r7)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

theorem mov0_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (imm 0)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

end

theorem open_rel {s₀ s₀' : State} (h0 : openArm.pre s₀) (h0' : openArm.pre s₀') (hq : openArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «open» fun _ _ => True := by
  have h6 : onePre 6 s₀ := h0
  have h6' : onePre 6 s₀' := h0'
  have hq6 : onePub 6 s₀ s₀' := hq.1
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  have L := oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 6 ∈ s₀.rd := by rw [h6.1]; simp
  have hin' : args s₀' 6 ∈ s₀'.rd := by rw [h6'.1]; simp
  have e4 : arg s₀' 4 = arg s₀ 4 := (qa 4 (by decide)).symm
  have h5' : (arg s₀' 5).toNat = (arg s₀ 5).toNat := by rw [qa 5 (by decide)]
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 4
  have r11 : ∀ {t₀ s : State}, OF 6 s₀ t₀ s → W s := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  let G1 : State → State → Prop := fun t₀ s => SO1 6 t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg s₀ 5).toNat
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G1 s₀) (G' := G1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 6)) (c := .block (oneEntry ++ [.ldrSp .r6 20]))
    (one_entry_agree (by simp) h6 h6' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact open1_wp h6)
    (fun s e => by rw [e]; exact WP.mono (open1_wp h6') fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, h5']⟩)
  let G2 : State → State → Prop := fun t₀ s => SO1 6 t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (arg s₀ 5).toNat
  have tl : ∀ {t₀ s : State}, G1 t₀ s → WP isa tagLenOk s (G2 t₀) := fun {t₀ s} ⟨h1, h6r⟩ =>
    WP.mono (tagLenOk_ok h6r (arg s₀ 5).isLt) fun s' ⟨hz, g, k⟩ => ⟨h1.keep (fun r a _ => g r a) k, hz⟩
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  have b := rel_wp (F := G1 s₀) (F' := G1 s₀') (G := G2 s₀) (G' := G2 s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tl h) (fun s h => tl h)
  -- the branches
  let rest6 : Prog isa := .seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.block [])
  let rest5 : Prog isa := .seq (cmp uO) rest6
  let rest4 : Prog isa := .seq recv rest5
  let rest3 : Prog isa := .seq (.block [.ldrSp .r6 20]) rest4
  let rest2 : Prog isa := .seq (oneTag uO) rest3
  let Z : State → State → Prop := fun t₀ s => s.z = decide (¬openTagOk t₀)
  have mid : RelCT isa (fun a b => G2 s₀ a ∧ G2 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) openGood) fun a b => W a ∧ W b := by
    refine rel_iteQ (!Spec.Gcm.tagLenOk (arg s₀ 5).toNat) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := G2 s₀) (F' := G2 s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => mov0_wp h.1.env.r11) (fun s h => mov0_wp (by rw [h.1.env.r11, e4]))
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = true := by simpa using hb
      have hok' : Spec.Gcm.tagLenOk (arg s₀' 5).toNat = true := by rw [h5']; exact hok
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      have eZ : decide (¬openTagOk s₀') = decide (¬openTagOk s₀) := by
        rw [decide_not, decide_not, ← openRes_isSome hok, ← openRes_isSome hok', hq.2]
      -- what each run reaches: whether the tags are equal
      have pfx : ∀ {t₀ s : State}, onePre 6 t₀ → Spec.Gcm.tagLenOk (arg t₀ 5).toNat = true → SO1 6 t₀ s →
          WP isa (.seq oneAad rest2) s (Z t₀) := fun ht hk h2 =>
        open_head ht h2 hk (T := .block []) fun s₈ om => WP.block_nil om.z
      have y1 := rel_ghost (R := rest2) (Z := Z s₀) (Z' := Z s₀') (oneAad_rel h6 h6' hq6 (by decide))
      have y2 := rel_ghost (R := rest3) (Z := Z s₀) (Z' := Z s₀')
        (oneTag_rel h6 h6' hq6 (by decide) (o := uO) (.inr rfl))
      have y3 := rel_ghost (R := rest4) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree (F := OF 6 s₀ s₀) (F' := OF 6 s₀ s₀')
          (G := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀)
          (G' := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀')
          (argTaint [] (4 * 6)) (c := .block [.ldrSp .r6 20])
          (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (one_hw h6) (one_hw h6') (rs := [])
            (by simp)) ⟨_, by taint_decide⟩
          (fun s h => ld6_wp spf hin rfl h) (fun s h => ld6_wp spf' hin' h5' h))
      have hD : ∀ {d k : Nat}, d + k ≤ 2560 →
          (args s₀ 6).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h6.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      have hD' : ∀ {d k : Nat}, d + k ≤ 2560 →
          (args s₀' 6).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ := fun hd => by
        rw [← e4]; exact (h6'.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      obtain ⟨_, c4⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) recv h).isSome = true := ⟨_, by taint_decide⟩
      have y4 := rel_ghost (R := rest5) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp
          (F := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀)
          (F' := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀')
          (G := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀)
          (G' := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h.2.2]
            · rw [r11 h.1.1, r11 h.2.1]) c4)
          (fun s h => recv_wp L spf (hD (by decide)) t1 t16 h) (fun s h => recv_wp L spf' (hD' (by decide)) t1 t16 h))
      obtain ⟨_, c5⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp uO) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have y5 := rel_ghost (R := rest6) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp
          (F := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀)
          (F' := P6 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat s₀')
          (G := P7 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat s₀)
          (G' := P7 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h.2.2]
            · rw [r11 h.1.1, r11 h.2.1]) c5)
          (fun s h => cmp_wp L spf (.inr rfl) (hD (by decide)) t1 t16 h)
          (fun s h => cmp_wp L spf' (.inr rfl) (hD' (by decide)) t1 t16 h))
      obtain ⟨_, c6⟩ : ∃ h, (taint.check (Taint.ofRegs [])
          (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
      have y6 := rel_ghost (R := .block []) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp (F := P7 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat s₀)
          (F' := P7 (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat s₀')
          (G := OF 6 s₀ s₀) (G' := OF 6 s₀ s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp at hr) c6)
          (fun s h => blk_wp h) (fun s h => blk_wp h))
      -- the data decrypted only if the tags are equal, which is public
      have y7 : RelCT isa (fun a b => (OF 6 s₀ s₀ a ∧ WP isa (.block []) a (Z s₀)) ∧
          (OF 6 s₀ s₀' b ∧ WP isa (.block []) b (Z s₀'))) (.ite .eq (.block []) oneCrypt) fun a b => W a ∧ W b :=
        rel_iteQ (decide (¬openTagOk s₀)) (fun s h => wp_nil h.2) (fun s h => (wp_nil h.2).trans eZ)
          (fun _ => RelCT.block_nil fun x y h => ⟨r11 h.1.1, r11 h.2.1⟩)
          (fun _ => (oneCrypt_rel h6 h6' hq6 (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
            fun _ _ h => ⟨r11 h.1, r11 h.2⟩)
      obtain ⟨_, c8⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block [.mov .r0 (.reg .r7)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have y8 := rel_wp (F := W) (F' := W) (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) c8)
        (fun s h => mov07_wp h) (fun s h => mov07_wp h)
      refine RelCT.mono (y1.seq (y2.seq (y3.seq (y4.seq (y5.seq (y6.seq (y7.seq y8))))))) (fun s s' h => ?_)
        fun _ _ h => h
      exact ⟨⟨h.1.1, pfx h6 hok h.1.1⟩, ⟨h.2.1, pfx h6' hok' h.2.1⟩⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) hB
  exact a.seq (b.seq (mid.seq d))

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

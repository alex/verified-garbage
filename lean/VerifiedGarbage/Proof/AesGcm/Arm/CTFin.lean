import VerifiedGarbage.Proof.AesGcm.Arm.CTCryptFn
import VerifiedGarbage.Proof.AesGcm.Arm.StreamVerify

/-!
# AES-GCM on ARMv7: `finTag`, `vg_aes_gcm_stream_finish` and `vg_aes_gcm_stream_verify` are constant time

Untrusted: everything here is checked by Lean. `verify` compares the tags
without a branch: only the tag length decides which code runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

/-- What `finTag` needs, in a run from `s₀`. -/
def FT (na : Nat) (s₀ : State) (c st w sp : BitVec 32) (R : Nat) (s : State) : Prop :=
  ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s ∧ ArgsKeep na s₀ s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_rel {na : Nat} (hna : 4 ≤ na) {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {s₀ s₀' : State} (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hsp : s₀.sp = s₀'.sp)
    (ha : ∀ i < na, arg s₀ i = arg s₀' i) (hw : ∀ r ∈ s₀.wr, (args s₀ na).Disjoint r)
    (hw' : ∀ r ∈ s₀'.wr, (args s₀' na).Disjoint r) (hin : args s₀ na ∈ s₀.rd) (hin' : args s₀' na ∈ s₀'.rd)
    (hA : ∀ r ∈ tagFrame st w sp o, (args s₀ na).Disjoint r) (hA' : ∀ r ∈ tagFrame st w sp o, (args s₀' na).Disjoint r) :
    RelCT isa (fun a b => FT na s₀ c st w sp R a ∧ FT na s₀' c st w sp R b) (finTag o) fun _ _ => True := by
  have hf' : s₀'.sp.toNat + 4 * na ≤ 2 ^ 32 := by rw [← hsp]; exact hf
  have ag : ∀ {s s'}, ArgsKeep na s₀ s → ArgsKeep na s₀' s' →
      VG.Arm.Taint.Agree (argTaint [] (4 * 4)) s s' := fun k k' =>
    (k.weaken hna).agree (k'.weaken hna) hsp (by omega) (fun i hi => ha i (by omega))
      (fun r hr => (hw r hr).sub_left (args_sub _ hna)) (fun r hr => (hw' r hr).sub_left (args_sub _ hna)) (by simp)
  have keep : ∀ {s s' : State} {k7 : BitVec 32} (rs : List Reg), Env c st w sp k7 (BitVec.ofNat 32 R) s →
      (∀ r, r ∉ rs → s'.gpr r = s.gpr r) → (∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], r ∉ rs) → Keeps s s' →
      Env c st w sp k7 (BitVec.ofNat 32 R) s' := fun rs he hg hn hK =>
    he.keep (fun r hr => hg r (hn r hr)) hK.sp hK.rd hK.wr
  -- whether there is text
  let GA : State → State → Prop := fun t₀ s => FT na t₀ c st w sp R s ∧
    s.z = decide ((arg t₀ 3 ++ arg t₀ 2).toNat = 0)
  have runA : ∀ {t₀ s : State}, FT na t₀ c st w sp R s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd →
      WP isa (.block tlenZero) s (GA t₀) := fun {t₀ s} ⟨k7, he, hk⟩ f i => by
    obtain ⟨i2, v2⟩ := hk.at f i 2 (by omega) (show 4 * 2 = 8 from rfl)
    obtain ⟨i3, v3⟩ := hk.at f i 3 (by omega) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_subFlags]) rfl rfl rfl,
      hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
    rw [z_sub0]
    exact decide_eq_decide.mpr (or_zero_iff _ _)
  have a := rel_agree (F := FT na s₀ c st w sp R) (F' := FT na s₀' c st w sp R) (G := GA s₀) (G' := GA s₀')
    (argTaint [] (4 * 4)) (c := .block tlenZero)
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runA h hf hin) (fun s h => runA h hf' hin')
  refine a.seq ?_
  -- the buffered bytes' length
  let v : State → BitVec 32 := fun t₀ => if (arg t₀ 3 ++ arg t₀ 2).toNat = 0 then arg t₀ 0 else arg t₀ 2
  let GB : State → State → Prop := fun t₀ s => FT na t₀ c st w sp R s ∧ s.gpr .r6 = v t₀
  have runB : ∀ {t₀ s : State}, GA t₀ s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd →
      WP isa (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8])) s (GB t₀) :=
    fun {t₀ s} ⟨⟨k7, he, hk⟩, hz⟩ f i => by
    refine WP.ite _ (eval_eq' hz) (fun ht => ?_) (fun hf₀ => ?_)
    · obtain ⟨i0, v0⟩ := hk.at f i 0 (by omega) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (arg t₀ 3 ++ arg t₀ 2).toNat = 0 := by simpa using ht
      simp [gpr_setReg, v0, v, this]
    · obtain ⟨i2, v2⟩ := hk.at f i 2 (by omega) (show 4 * 2 = 8 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2, v2], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (arg t₀ 3 ++ arg t₀ 2).toNat ≠ 0 := by simpa using hf₀
      simp [gpr_setReg, v2, v, this]
  have b : RelCT isa (fun a b => GA s₀ a ∧ GA s₀' b) (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8]))
      fun _ _ => True := by
    refine rel_ite (decide ((arg s₀ 3 ++ arg s₀ 2).toNat = 0)) (fun s h => h.2)
      (fun s h => by rw [h.2, ha 3 (by omega), ha 2 (by omega)]) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (argTaint [] (4 * 4)) (.block [.ldrSp .r6 0]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := taint) (argTaint [] (4 * 4)) (fun s s' h =>
        ag h.1.1.choose_spec.2 h.2.1.choose_spec.2) hc
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (argTaint [] (4 * 4)) (.block [.ldrSp .r6 8]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := taint) (argTaint [] (4 * 4)) (fun s s' h =>
        ag h.1.1.choose_spec.2 h.2.1.choose_spec.2) hc
  refine (rel_wp b (fun s h => runB h hf hin) (fun s h => runB h hf' hin')).seq ?_
  have hv : v s₀' = v s₀ := by simp only [v, ha 0 (by omega), ha 2 (by omega), ha 3 (by omega)]
  -- modulo 16
  let GC : State → State → Prop := fun t₀ s => FT na t₀ c st w sp R s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((v s₀).toNat % 16)
  have runC : ∀ {t₀ s : State}, v t₀ = v s₀ → GB t₀ s → WP isa (.block [.dp .and .r6 .r6 (imm 15)]) s (GC t₀) :=
    fun {t₀ s} e ⟨⟨k7, he, hk⟩, h6⟩ => by
    refine WP.of_runBlock ⟨_, by arun [], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [gpr_setReg, ite_true, h6, and15, e]
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) (.block [.dp .and .r6 .r6 (imm 15)]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have cC := rel_wp (F := GB s₀) (F' := GB s₀') (G := GC s₀) (G' := GC s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s s' h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hv]) hC)
    (fun s h => runC rfl h) (fun s h => runC hv h)
  refine cC.seq ?_
  -- the buffered bytes padded
  have runF : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → (∀ r ∈ tagFrame st w sp o, (args t₀ na).Disjoint r) →
      GC t₀ s → WP isa (flush 16) s (FT na t₀ c st w sp R) := fun {t₀ s} f hA₀ ⟨⟨k7, he, hk⟩, h6⟩ => by
    have hq := Nat.mod_lt (v s₀).toNat (show 16 > 0 by decide)
    refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate ((v s₀).toNat % 16) 0)
      (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
      fun s' ⟨fl, rd, wr, sp'⟩ => ⟨k7, fl.env, hk.frame f fl.frame (disj_sub hA₀ tFrame_sub) sp' rd wr⟩
  have cF := rel_wp (F := GC s₀) (F' := GC s₀') (G := FT na s₀ c st w sp R) (G' := FT na s₀' c st w sp R)
    (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (v s₀).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => runF hf hA h) (fun s h => runF hf' hA' h)
  refine cF.seq ?_
  -- the lengths
  have runD : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd → FT na t₀ c st w sp R s →
      WP isa (.block [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12]) s (FT na t₀ c st w sp R) :=
    fun {t₀ s} f i ⟨k7, he, hk⟩ => by
    obtain ⟨j0, w0⟩ := hk.at f i 0 (by omega) (show 4 * 0 = 0 from rfl)
    obtain ⟨j1, w1⟩ := hk.at f i 1 (by omega) (show 4 * 1 = 4 from rfl)
    obtain ⟨j2, w2⟩ := hk.at f i 2 (by omega) (show 4 * 2 = 8 from rfl)
    obtain ⟨j3, w3⟩ := hk.at f i 3 (by omega) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by arun [j0, w0, j1, w1, j2, w2, j3, w3], ?_⟩
    exact ⟨_, he.set7 (k7' := arg t₀ 3) (by simp [gpr_setReg, w3]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩
  have cD := rel_agree (F := FT na s₀ c st w sp R) (F' := FT na s₀' c st w sp R) (G := FT na s₀ c st w sp R)
    (G' := FT na s₀' c st w sp R) (argTaint [] (4 * 4))
    (c := .block [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12])
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runD hf hin h) (fun s h => runD hf' hin' h)
  exact cD.seq (rel_of_ct (tag_ct L ho hR) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩))

end

theorem fin_hw {n : Nat} {t : State} (ht : finPre n t) : ∀ r ∈ t.wr, (args t n).Disjoint r := by
  obtain ⟨-, hwr, -, -, -, dsA, dWA, -⟩ := ht
  intro r hr
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact dsA.symm
  · exact dWA.symm

theorem fin_entry_agree {n : Nat} {s₀ s₀' : State} (h0 : finPre n s₀) (h0' : finPre n s₀') (hq : finPub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2] (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀ h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 qa (fin_hw h0) (fin_hw h0')
    fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem streamFinish_rel {s₀ s₀' : State} (h0 : streamFinishArm.pre s₀) (h0' : streamFinishArm.pre s₀')
    (hq : streamFinishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamFinish fun _ _ => True := by
  have h0₅ : finPre 5 s₀ := h0
  have h0₅' : finPre 5 s₀' := h0'
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := id hq
  have L := finLay h0₅
  have hR := h0₅.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h0₅.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SF1 5 s₀) (G' := SF1 5 s₀')
    (argTaint [.r0, .r1, .r2] (4 * 5)) (c := .block finEntry) (fin_entry_agree h0₅ h0₅' hq) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact fin1_wp h0₅ (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact fin1_wp h0₅' (by decide) fun _ h => h)
  let G : State → Prop := fun s => ∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp k7 k8 s
  have tg : ∀ {t₀ : State}, finPre 5 t₀ → t₀.sp = s₀.sp → arg t₀ 4 = arg s₀ 4 → t₀.gpr .r0 = s₀.gpr .r0 →
      t₀.gpr .r2 = s₀.gpr .r2 → ∀ s, SF1 5 t₀ s → WP isa (finTag 0) s G := fun {t₀} ht e0 e4 er0 er2 s h1 =>
    WP.mono (fin_tag ht (by decide) h1 (.inl rfl) (a := List.replicate ((arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0) (by simp) (by simp)) fun s' h => by
      obtain ⟨k7, he⟩ := h.env
      rw [e0, e4, er0, er2] at he
      exact ⟨k7, _, he⟩
  have e1 : BitVec.ofNat 32 (s₀.gpr .r1).toNat = s₀.gpr .r1 := by simp
  have b := rel_wp (F := SF1 5 s₀) (F' := SF1 5 s₀') (G := G) (G' := G)
    (finTag_rel L (na := 5) (by decide) (o := 0) (.inl rfl) hR spf q₀ qa (fin_hw h0₅) (fin_hw h0₅')
      (by rw [h0₅.1]; simp) (by rw [h0₅'.1]; simp) (fin_argsTag h0₅ (.inl rfl))
      (by have := fin_argsTag h0₅' (o := 0) (.inl rfl); rwa [← q₃, ← qa 4 (by decide), ← q₀] at this) |>.mono
      (fun s s' ⟨h₁, h₂⟩ => ⟨⟨_, by rw [e1]; exact h₁.env, h₁.args⟩, ⟨_, by
        have := h₂.env; rw [← q₁, ← q₂, ← q₃, ← qa 4 (by decide), ← q₀] at this; rw [e1]; exact this, h₂.args⟩⟩)
      fun _ _ h => h)
    (tg h0₅ rfl rfl rfl rfl) (tg h0₅' q₀.symm (qa 4 (by decide)).symm q₁.symm q₃.symm)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have c := RelCT.taint (A := taint) (P := fun s₁ s₂ => G s₁ ∧ G s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hB
  exact a.seq (b.seq c)

theorem streamFinish_ct : ConstantTime isa streamFinishArm.pre streamFinishArm.pub streamFinish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamFinish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

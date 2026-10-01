import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBounded

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_bounded_poly`, constant time but for which half-bytes it accepts

Untrusted: everything here is checked by Lean. Two runs whose leaks agree
(which half-bytes of the first 1088 bytes of output are accepted,
`rejBoundedLeak`) and whose pointers and `η` agree leak the same, piece by
piece (`Rel.lean`): the prologue, the sponge and the end by the taint
analysis, and the loop iteration by iteration. At iteration `t`, both runs
have sampled as many coefficients (`rbFold_length_congr`, from
`leak_hbOks`), so `x3` and `x4` agree, and so does whether each half-byte
of byte `t` is accepted: each branch goes the same way, and each store to
the same address. Each piece between the branches is proved constant time
by the taint analysis from `x2` or `x3`, and correctness then describes
where both runs are (`relTaintStep`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_nil wp_subImm eval_zero eval_nonzero eq_zero_iff ne_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H halfByteOk maxBounds n)
open VG.Spec.Sha3 (bytesAt)

namespace RejBounded

section
variable {σ₁ σ₂ : State} (hq : rbK.pub σ₁ σ₂)
include hq

theorem pub_eq : spOf σ₁ = spOf σ₂ := by
  rw [spOf, spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]

theorem eta_eq : etaOf σ₁ = etaOf σ₂ := by simp only [etaOf, hq.2.1]

/-- The two outputs are accepted alike. -/
theorem oks_eq : (X σ₁).map (hbOks (etaOf σ₁)) = (X σ₂).map (hbOks (etaOf σ₂)) := by
  have h := hq.2.2.2.2.2
  rw [eta_eq hq] at h ⊢
  exact leak_hbOks h (by decide)

theorem len_eq (t : Nat) : (Lt σ₁ t).length = (Lt σ₂ t).length := by
  have h := oks_eq hq
  rw [eta_eq hq] at h
  simp only [Lt]
  rw [eta_eq hq]
  exact rbFold_length_congr rfl (by rw [List.map_take, List.map_take, h])

theorem hb_eq {t : Nat} (ht : t < 544) : hbOks (etaOf σ₁) (Z σ₁ t) = hbOks (etaOf σ₂) (Z σ₂ t) := by
  have := congrArg (fun L => L.getD t (0, 0)) (oks_eq hq)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Z] at this ⊢
  rw [List.getElem?_eq_getElem (by rw [X_length]; exact ht), List.getElem?_eq_getElem (by rw [X_length]; exact ht)]
    at this ⊢
  simpa using this

theorem lm_eq {t : Nat} (ht : t < 544) : (Lm σ₁ t).length = (Lm σ₂ t).length := by
  simp only [Lm]
  rw [hbTry_length, hbTry_length, len_eq hq]
  have := congrArg Prod.fst (hb_eq hq ht)
  simp only [hbOks] at this
  rw [this]

end

theorem taint_load : ∃ h, (taint.check (Taint.ofRegs [.x2]) (.block rbLoad) h).isSome = true := ⟨_, by taint_decide⟩

theorem taint_nil : ∃ h, (taint.check (Taint.ofRegs []) (.block ([] : List Instr)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem taint_lo {η : Nat} (hη : η = 2 ∨ η = 4) :
    ∃ h, (taint.check (Taint.ofRegs [.x3]) (.block (rbTry η ++ ([.lsr .x .x7 .x6 4] : List Instr))) h).isSome = true := by
  rcases hη with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem taint_hi {η : Nat} (hη : η = 2 ∨ η = 4) :
    ∃ h, (taint.check (Taint.ofRegs [.x3]) (.block (rbTry η)) h).isSome = true := by
  rcases hη with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

section
variable {η : Nat} (hη : η = 2 ∨ η = 4) {t : Nat} (ht : t < 544)
include hη ht

/-- An iteration, in two runs. -/
theorem body_ct : RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ LAt σ t s) (rbBody η)
    (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ LAt σ (t + 1) s) := by
  obtain ⟨_, tl⟩ := taint_load
  obtain ⟨_, tn⟩ := taint_nil
  obtain ⟨_, tlo⟩ := taint_lo hη
  obtain ⟨_, thi⟩ := taint_hi hη
  refine RelCT.seq (relTaintStep (J' := fun σ s => etaOf σ = η ∧ LB σ t s) [.x2]
    (fun σ s hp ⟨he, h⟩ => WP.mono (load_ok hp ht h) fun s' h' => ⟨he, h'⟩)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨_, h₁⟩ ⟨_, h₂⟩ => ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
      fun r hr => by rw [List.mem_singleton.mp hr, h₁.x2, h₂.x2, pub_eq hq]⟩) tl) ?_
  refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, _, _, hq, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => by
      rw [eval_x4 h₁.x4 (Lt_le σ₁ t), eval_x4 h₂.x4 (Lt_le σ₂ t), len_eq hq])
    (RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s => (etaOf σ = η ∧ LB σ t s) ∧ (Lt σ t).length = 256)
      (relTaintStep [] (fun σ s hp ⟨⟨he, h⟩, hl⟩ => wp_nil ⟨he, full ht h hl⟩)
        (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, h₁⟩, _⟩ ⟨⟨_, h₂⟩, _⟩ =>
          ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1], fun r hr => absurd hr List.not_mem_nil⟩) tn)
      (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩, hc⟩ => by
        rw [eval_x4 h₁.x4 (Lt_le σ₁ t)] at hc
        have hl : (Lt σ₁ t).length = 256 := by simpa using hc
        exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, h₁⟩, hl⟩, ⟨⟨e₂, h₂⟩, by rw [← len_eq hq]; exact hl⟩⟩)
      fun _ _ h => h) ?_
  refine RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s => (etaOf σ = η ∧ LB σ t s) ∧ (Lt σ t).length < 256)
    ?_ (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩, hc⟩ => by
      rw [eval_x4 h₁.x4 (Lt_le σ₁ t)] at hc
      have hl : (Lt σ₁ t).length ≠ 256 := by simpa using hc
      have := Lt_le σ₁ t
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, h₁⟩, by omega⟩, ⟨⟨e₂, h₂⟩, by rw [← len_eq hq]; omega⟩⟩)
    fun _ _ h => h
  refine RelCT.seq (relTaintStep (J' := fun σ s => etaOf σ = η ∧ (Lt σ t).length < 256 ∧ LM σ t s) [.x3]
    (fun σ s hp ⟨⟨he, h⟩, hl⟩ => by
      subst he; exact WP.mono (lo_ok hp h hl) fun s' h' => ⟨rfl, hl, h'⟩)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, h₁⟩, _⟩ ⟨⟨_, h₂⟩, _⟩ => ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
      fun r hr => by rw [List.mem_singleton.mp hr, h₁.x3, h₂.x3, len_eq hq, hq.2.2.1]⟩) tlo) ?_
  have hml : ∀ σ, (Lt σ t).length < 256 → (Lm σ t).length ≤ 256 := fun σ hl => by
    have := hbTry_length (etaOf σ) (Lt σ t) ((Z σ t).toNat % 16)
    have := halfByteOk_le (etaOf σ) ((Z σ t).toNat % 16)
    simp only [Lm]
    omega
  refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, _, _, hq, ⟨_, l₁, h₁⟩, ⟨_, l₂, h₂⟩⟩ => by
      rw [eval_x4 h₁.x4 (hml σ₁ l₁), eval_x4 h₂.x4 (hml σ₂ l₂), lm_eq hq ht])
    (RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s =>
        (etaOf σ = η ∧ (Lt σ t).length < 256 ∧ LM σ t s) ∧ (Lm σ t).length = 256)
      (relTaintStep [] (fun σ s hp ⟨⟨he, hl, h⟩, hm⟩ => wp_nil ⟨he, lo_full ht h hl hm⟩)
        (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, _, h₁⟩, _⟩ ⟨⟨_, _, h₂⟩, _⟩ =>
          ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1], fun r hr => absurd hr List.not_mem_nil⟩) tn)
      (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, l₁, h₁⟩, ⟨e₂, l₂, h₂⟩⟩, hc⟩ => by
        rw [eval_x4 h₁.x4 (hml σ₁ l₁)] at hc
        have hm : (Lm σ₁ t).length = 256 := by simpa using hc
        exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, l₁, h₁⟩, hm⟩, ⟨⟨e₂, l₂, h₂⟩, by rw [← lm_eq hq ht]; exact hm⟩⟩)
      fun _ _ h => h)
    (RelCT.mono (P := Rel2 rbK.pre rbK.pub fun σ s =>
        (etaOf σ = η ∧ (Lt σ t).length < 256 ∧ LM σ t s) ∧ (Lm σ t).length < 256)
      (relTaintStep [.x3] (fun σ s hp ⟨⟨he, _, h⟩, hm⟩ => by
          subst he; exact WP.mono (hi_ok hp ht h hm) fun s' h' => ⟨rfl, h'⟩)
        (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨⟨_, _, h₁⟩, _⟩ ⟨⟨_, _, h₂⟩, _⟩ =>
          ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
            fun r hr => by rw [List.mem_singleton.mp hr, h₁.x3, h₂.x3, lm_eq hq ht, hq.2.2.1]⟩) thi)
      (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, l₁, h₁⟩, ⟨e₂, l₂, h₂⟩⟩, hc⟩ => by
        rw [eval_x4 h₁.x4 (hml σ₁ l₁)] at hc
        have hm : (Lm σ₁ t).length ≠ 256 := by simpa using hc
        have := hml σ₁ l₁
        exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨e₁, l₁, h₁⟩, by omega⟩, ⟨⟨e₂, l₂, h₂⟩, by rw [← lm_eq hq ht]; omega⟩⟩)
      fun _ _ h => h)

end

/-- The loop's iterations, in two runs. -/
theorem iters_ct {η : Nat} (hη : η = 2 ∨ η = 4) :
    RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ LAt σ 0 s) (.loop (rbBody η) (.nonzero .x .x5))
      (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ LAt σ 544 s) := by
  let I : Nat → State → State → Prop := fun n =>
    Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ 0 < n ∧ n ≤ 544 ∧ LAt σ (544 - n) s
  refine RelCT.mono (RelCT.loop (M := isa) I (fun n => ?_) 544)
    (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, by decide, Nat.le_refl _, h₁⟩, ⟨e₂, by decide, Nat.le_refl _, h₂⟩⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 544
  · have ht : 544 - n < 544 := by omega
    refine RelCT.mono (body_ct hη ht) (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, _, _, h₁⟩, ⟨e₂, _, _, h₂⟩⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩) ?_
    intro s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩
    have c : ∀ {u : State}, (u.gpr .x5).toNat = 544 - (544 - n + 1) →
        isa.eval (.nonzero .x .x5) u = some (decide (n ≠ 1)) := fun h5 => by
      rw [eval_nonzero, ne_zero_iff, h5]
      exact congrArg some (decide_eq_decide.mpr (by omega))
    refine ⟨by rw [c h₁.x5, c h₂.x5], fun hf => ?_, fun htr => ?_⟩
    · rw [c h₁.x5] at hf
      have : n = 1 := by simpa using hf
      subst this
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩
    · rw [c h₁.x5] at htr
      have : n ≠ 1 := by simpa using htr
      refine ⟨n - 1, by omega, σ₁, σ₂, p₁, p₂, hq, ⟨e₁, by omega, by omega, ?_⟩, ⟨e₂, by omega, by omega, ?_⟩⟩
      · rw [show 544 - (n - 1) = 544 - n + 1 by omega]; exact h₁
      · rw [show 544 - (n - 1) = 544 - n + 1 by omega]; exact h₂
  · exact RelCT.of_false fun s₁ s₂ ⟨_, _, _, _, _, ⟨_, h1, h2, _⟩, _⟩ => hn ⟨h1, h2⟩

theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4) :
    RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => J6 136 544 (spOf σ) σ s ∧ etaOf σ = η) (rbLoop η)
      (Rel2 rbK.pre rbK.pub fun σ s => LAt σ 544 s) := by
  have ts : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27]) (.block (rbSetup η)) h).isSome = true := by
    rcases hη with rfl | rfl
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, ts⟩ := ts
  refine RelCT.mono (RelCT.seq (relTaintStep (J' := fun σ s => etaOf σ = η ∧ LAt σ 0 s) [.x25, .x26, .x27]
    (fun σ s hp ⟨h, he⟩ => by
      have := setup_ok hp h
      rw [he] at this
      exact WP.mono this fun s' h' => ⟨he, h'⟩)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq ⟨h₁, _⟩ ⟨h₂, _⟩ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.1], fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]⟩) ts) (iters_ct hη)) (fun _ _ h => h)
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩

theorem ctWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa rbK.pre rbK.pub (rejBoundedWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.mldsaBoundedTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 rbK.pre rbK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0, .x2, .x3]
    (fun σ s hp h => by subst h; exact pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      exact ⟨hq.2.2.2.2.1, RejNtt.regs3 hq.1 hq.2.2.1 hq.2.2.2.1⟩) (by taint_decide)) ?_
  refine RelCT.seq (relTaintStep (J' := fun σ => J6 136 544 (spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => spongeWith_ok (v := v) (spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
      · rw [h₁.x3, h₂.x3, pub_eq hq]
      · exact toNat_inj h₁.x4 h₂.x4) hhint) ?_
  refine RelCT.seq (RelCT.seq (relTaintStep (J' := fun σ s => J6 136 544 (spOf σ) σ s ∧
      isa.eval (.zero .x .x9) s = some (decide (etaOf σ = 2))) []
      (fun σ s hp h => wp_subImm (by decide) fun s₁ o₁ e₁ => wp_nil ⟨⟨h.env.keep o₁.keep o₁.mem,
        by rw [o₁.mem]; exact h.out⟩, by
          rw [eval_zero, eq_zero_iff, e₁, x27_eq h.env]
          rcases eta hp with he | he <;> rw [he] <;> rfl⟩)
      (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.1],
        fun r hr => absurd hr List.not_mem_nil⟩) (by taint_decide))
    (RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, _, _, hq, ⟨_, c₁⟩, ⟨_, c₂⟩⟩ => by rw [c₁, c₂, eta_eq hq])
      (RelCT.mono (rbLoop_ct (.inl rfl)) (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, hc⟩ => by
          rw [c₁] at hc
          have e : etaOf σ₁ = 2 := by simpa using hc
          exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, e⟩, ⟨h₂, by rw [← eta_eq hq]; exact e⟩⟩) fun _ _ h => h)
      (RelCT.mono (rbLoop_ct (.inr rfl)) (fun s₁ s₂ ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, hc⟩ => by
          rw [c₁] at hc
          have e : etaOf σ₁ ≠ 2 := by simpa using hc
          have e4 : etaOf σ₁ = 4 := (eta p₁).resolve_left e
          exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, e4⟩, ⟨h₂, by rw [← eta_eq hq]; exact e4⟩⟩) fun _ _ h => h))) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.base.env.sp, h₂.base.env.sp, hq.2.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.base.env.x25, h₂.base.env.x25, pub_eq hq]⟩) (by taint_decide)

theorem ct : ConstantTime isa rbK.pre rbK.pub rejBounded :=
  ctWith .scalar

end RejBounded

/-- A state satisfying the precondition. -/
def rbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 2 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejBounded_verifiedWith (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target (Impl.MlDsa.AArch64.Sample.rejBoundedWith v.callee)
    (Spec.MlDsa.rejBoundedContract AArch64.abi 16) :=
  Verified.of_correct (RejBounded.correctWith v) (RejBounded.ctWith v)
    { pre := by sig_implies_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK, AArch64.abi,
          AArch64.argRegs]
        dsimp only [rbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
            show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
            rw [rejBounded_some _ hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.rejBoundedPoly _ Spec.MlDsa.minBounds.rejBounded _) = none
              rw [rejBounded_none (B := 544) _ (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK, AArch64.abi,
          AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2, hx3⟩ := h
        exact ⟨hx0, hx1, hx2, hx3, hsp, hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK,
        AArch64.abi, AArch64.argRegs] [rbSat] using rbSat }

theorem rejBounded_verified : Verified AArch64.target Impl.MlDsa.AArch64.Sample.rejBounded
    (Spec.MlDsa.rejBoundedContract AArch64.abi 16) :=
  rejBounded_verifiedWith .scalar

end VG.Proof.MlDsa.AArch64.Sample

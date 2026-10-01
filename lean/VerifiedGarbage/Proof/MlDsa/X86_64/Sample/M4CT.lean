import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Top

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, constant time

Untrusted: everything here is checked by Lean. Two runs whose pointers and
`γ₁` agree (the declared public data) leak the same. The taint analysis
proves each piece from the pointers (the prologue, the absorption and the
squeezes, from the arguments and then `rbx`; the unpackings, from `rbx`,
`r13` and `rsp`); the two runs take the same branch on `γ₁` (`cmp_ok`), as
their `γ₁` agree.
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (oRc)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emOk gOf)
open VG.Proof.MlDsa.Sample (emC)

/-- Two runs related by `I`, from entry states that agree on what is public. -/
abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 em4K.pre em4K.pub I

theorem env_rbx {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : Env σ₁ s₁) (e₂ : Env σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx := by rw [e₁.rbx, e₂.rbx, scr, scr, hq.2.2.2.1]

theorem env_r13 {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : Env σ₁ s₁) (e₂ : Env σ₂ s₂) :
    s₁.gpr .r13 = s₂.gpr .r13 := by rw [e₁.r13, e₂.r13, aP, aP, hq.2.2.1]

theorem env_rsp {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : Env σ₁ s₁) (e₂ : Env σ₂ s₂) :
    s₁.gpr .rsp = s₂.gpr .rsp := by rw [e₁.rsp, e₂.rsp, hq.2.2.2.2]

/-- `squeeze4 n`, given its taint analysis. -/
theorem sq_ct (n : Nat) (hn : n < 5) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (R fun σ s => SqInv σ n s) (squeeze4 n) (R fun σ s => SqInv σ (n + 1) s) :=
  relInv (fun σ s hp h => sq_ok (pre_of hp) hn h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) c)

/-- The branch on `γ₁`'s comparison, and what it keeps. -/
theorem cmp_ok {σ : State} {s : State} (h : SqInv σ 5 s) :
    WP isa (.block [.vop .vzeroupper, .alu32 .cmp .r14 (.imm 0x20000)]) s fun s' =>
      (∀ c, UI σ c 0 s') ∧ s'.zf = some (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0) := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r14) - 0x20000 == 0)) (by xrun; exact ⟨rfl, rfl, rfl⟩) (by decide))
    fun s1 ⟨⟨hm1, h14, hz1⟩, k1'⟩ => ⟨fun c => ⟨Env.low h.env (rs := []) (by simp)
      (by rw [hm1]; exact Frame.refl _ _) k1'.2.1 k1'.2.2 fun r _ => by
        by_cases e : r = .r14
        · subst e; exact h14
        · exact k1'.gpr (by simp [e]),
      fun k hk p hp' => by rw [hm1]; exact h.buf k hk p (by omega), fun _ hk => absurd hk (by omega)⟩,
    by rw [hz1, h.env.r14]⟩

/-- The comparison of `γ₁`, as `γ₁ = 2¹⁷`. -/
theorem zf_gamma (σ : State) :
    (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0) = decide (gOf σ = 2 ^ 17) := by
  by_cases e : gOf σ = 2 ^ 17
  · rw [show BitVec.setWidth 32 (σ.gpr .rsi) = 0x20000 from BitVec.eq_of_toNat_eq (by rw [← gOf, e]; rfl),
      decide_eq_true e]
    rfl
  · rw [decide_eq_false e, beq_eq_false_iff_ne]
    intro h
    apply e
    rw [gOf, show BitVec.setWidth 32 (σ.gpr .rsi) = 0x20000 by
      rw [← BitVec.sub_add_cancel (BitVec.setWidth 32 (σ.gpr .rsi)) 0x20000, h]; rfl]
    rfl

/-- A piece that takes each run from `I` to `I'`, keeping a fact `C` of the entry states. -/
theorem relInvC {I I' : State → State → Prop} {C : State → Prop} {c : Prog isa}
    (hw : ∀ σ s, em4K.pre σ → I σ s → WP isa c s (I' σ)) (ht : RelCT isa (R I) c fun _ _ => True) :
    RelCT isa (R fun σ s => I σ s ∧ C σ) c (R fun σ s => I' σ s ∧ C σ) :=
  relInv (fun σ s hp hs => WP.mono (hw σ s hp hs.1) fun _ h => ⟨h, hs.2⟩)
    (RelCT.mono ht (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h)

/-- The unpackings for `c`, from states with the same pointers, keeping a fact `C` of the entry states. -/
theorem unpack4_ct {c : Nat} (hc : emOk c) {C : State → Prop} {hh : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13, .rsp]) (unpack4 c) hh).isSome = true) :
    RelCT isa (R fun σ s => UI σ c 0 s ∧ C σ) (unpack4 c) (R fun σ s => UI σ c 4 s ∧ C σ) :=
  relInvC (fun σ s hp h => unpack4_ok (pre_of hp) hc h)
    (taintRel [.rbx, .r13, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [env_rbx hq h₁.env h₂.env, env_r13 hq h₁.env h₂.env, env_rsp hq h₁.env h₂.env]) ht)

theorem gOf_pub {σ₁ σ₂ : State} (hq : em4K.pub σ₁ σ₂) : gOf σ₁ = gOf σ₂ := by rw [gOf, gOf, hq.2.1]

/-- The branch on `γ₁`. -/
theorem sel_ct : RelCT isa (R fun σ s => (∀ c, UI σ c 0 s) ∧
      s.zf = some (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0))
    (.ite .e (unpack4 18) (unpack4 20)) (R fun σ s => UI σ (emC (gOf σ)) 4 s) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
      show x.zf = y.zf; rw [h₁.2, h₂.2, hq.2.1]) ?_ ?_
  · refine RelCT.mono (unpack4_ct (C := fun σ => emC (gOf σ) = 18) (.inl rfl) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨u₁, c₁⟩, ⟨u₂, c₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, by show UI σ₁ _ 4 x; rw [c₁]; exact u₁,
        by show UI σ₂ _ 4 y; rw [c₂]; exact u₂⟩
    have hb' : x.zf = some true := hb
    rw [h₁.2, zf_gamma, Option.some.injEq, decide_eq_true_iff] at hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.1 18, by rw [hb']; rfl⟩, ⟨h₂.1 18, by rw [← gOf_pub hq, hb']; rfl⟩⟩
  · refine RelCT.mono (unpack4_ct (C := fun σ => emC (gOf σ) = 20) (.inr rfl) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨u₁, c₁⟩, ⟨u₂, c₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, by show UI σ₁ _ 4 x; rw [c₁]; exact u₁,
        by show UI σ₂ _ 4 y; rw [c₂]; exact u₂⟩
    have hb' : x.zf = some false := hb
    rw [h₁.2, zf_gamma, Option.some.injEq, decide_eq_false_iff_not] at hb'
    have e₁ : gOf σ₁ = 2 ^ 19 := (pre_of p₁).gamma.resolve_left hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.1 20, by rw [e₁]; rfl⟩, ⟨h₂.1 20, by rw [← gOf_pub hq, e₁]; rfl⟩⟩

theorem ct : ConstantTime isa em4K.pre em4K.pub expandMask4Avx2 := by
  unfold expandMask4Avx2
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ s => SqInv σ 0 s)
    (fun σ s hp h => by subst h; exact start_ok (pre_of hp))
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]) (by taint_decide))) ?_)
  refine RelCT.seq (sq_ct 0 (by decide) (by taint_decide)) (RelCT.seq (sq_ct 1 (by decide) (by taint_decide))
    (RelCT.seq (sq_ct 2 (by decide) (by taint_decide)) (RelCT.seq (sq_ct 3 (by decide) (by taint_decide))
      (RelCT.seq (sq_ct 4 (by decide) (by taint_decide)) ?_))))
  refine RelCT.seq (relInv (fun σ s _ h => cmp_ok h) (taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide))) (RelCT.seq sel_ct ?_)
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Mask4

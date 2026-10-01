import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA

/-!
# ML-DSA signing on AArch64: two runs

Untrusted: everything here is checked by Lean. Constant time is proven
piece by piece (`RelCT`) for two runs from entry states that satisfy
`signK`'s precondition and agree on its public data, each satisfying the
invariant `I` of the correctness proof, and related by `E` (`RR`): each
piece leaks the same, correctness gives each run's next invariant, and the
piece's own proof the next relation (`relInvE`). The runs are in the same
layout (`RR.lrel`) and agree on `ρ` (`RR.rho`), which the leakage begins
with.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (D : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  Rel2 (signK p D).pre (signK p D).pub I x y ∧ E x y

section
variable {p : Params} {D : Nat}

/-- Two runs in the same layout: their entry states agree on the pointers. -/
theorem lrel_of {σ₁ σ₂ x y : State} (hpub : (signK p D).pub σ₁ σ₂) (S₁ : St p D σ₁ x) (S₂ : St p D σ₂ y) :
    LRel D (sgR p) (sgW p) x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun r hr => ?_, by rw [S₁.top.sp, S₂.top.sp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ (.x23, .x3) (by decide), r₂ (.x23, .x3) (by decide), h4]
  · rw [r₁ (.x25, .x0) (by decide), r₂ (.x25, .x0) (by decide), h1]
  · rw [r₁ (.x26, .x1) (by decide), r₂ (.x26, .x1) (by decide), h2]
  · rw [r₁ (.x27, .x2) (by decide), r₂ (.x27, .x2) (by decide), h3]
  · rw [r₁ (.x28, .x4) (by decide), r₂ (.x28, .x4) (by decide), h5]

theorem relInvE {I J E E' : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (RR p D I E) c E') : RelCT isa (RR p D I E) c (RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', he⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, he⟩

theorem RR.mono {I I' E E' : State → State → Prop} {x y : State} (h : RR p D I E x y)
    (hI : ∀ σ s, I σ s → I' σ s) (hE : E x y → E' x y) : RR p D I' E' x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, e⟩ := h
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, hI _ _ i₁, hI _ _ i₂⟩, hE e⟩

theorem RR.lrel {I E : State → State → Prop} (hI : ∀ σ s, I σ s → St p D σ s) {x y : State}
    (h : RR p D I E x y) : LRel D (sgR p) (sgW p) x y := by
  obtain ⟨⟨σ₁, σ₂, _, _, hpub, i₁, i₂⟩, _⟩ := h
  exact lrel_of hpub (hI _ _ i₁) (hI _ _ i₂)

theorem WP.conj {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨t, s', e, q₁⟩ := h₁
  obtain ⟨_, _, e', q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, _, e, q₁, q₂⟩

/-- A piece that takes each run from `I` to `J` and from `s` to `s'` with
`F s s'`, and leaks the same from runs related by `RR p D I E`, with `Q₀` of
the final states. -/
theorem stepRR {I J E E' Q₀ F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (RR p D I E) c Q₀)
    (hE : ∀ x y x' y', RR p D I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (RR p D I E) c (RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ := hr
  obtain ⟨_, u₁, f₁, g₁, k₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂, k₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, hE _ _ _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ k₁ k₂ hq⟩

end

/-! ## Runs related through their entry states -/

/-- Two runs, each satisfying `I` from its entry state, the entry states related by `E`. -/
def RS (p : Params) (D : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  ∃ σ₁ σ₂, (signK p D).pre σ₁ ∧ (signK p D).pre σ₂ ∧ (signK p D).pub σ₁ σ₂ ∧ E σ₁ σ₂ ∧ I σ₁ x ∧ I σ₂ y

section
variable {p : Params} {D : Nat}

theorem RS.lrel {E I : State → State → Prop} (hI : ∀ σ s, I σ s → St p D σ s) {x y : State}
    (h : RS p D E I x y) : LRel D (sgR p) (sgW p) x y := by
  obtain ⟨σ₁, σ₂, _, _, hpub, _, i₁, i₂⟩ := h
  exact lrel_of hpub (hI _ _ i₁) (hI _ _ i₂)

theorem RS.mono {E I E' I' : State → State → Prop} {x y : State} (h : RS p D E I x y)
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → E' σ₁ σ₂) (hI : ∀ σ s, I σ s → I' σ s) : RS p D E' I' x y := by
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, e, i₁, i₂⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, hE _ _ e, hI _ _ i₁, hI _ _ i₂⟩

/-- A piece that leaks the same from two runs in the layout that satisfy `T`, and takes each run from
`I` to `J`. -/
theorem liftL {E I J : State → State → Prop} {T : State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → St p D σ s ∧ T s) (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ T x ∧ T y) c fun _ _ => True) :
    RelCT isa (RS p D E I) c (RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ ⟨lrel_of hpub (hI _ _ i₁).1 (hI _ _ i₂).1, (hI _ _ i₁).2, (hI _ _ i₂).2⟩ e₁ e₂
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- `liftL`, with a leakage proof from any relation the runs satisfy. -/
theorem liftR {E I J : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (RS p D E I) c fun _ _ => True) : RelCT isa (RS p D E I) c (RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- Two pieces in sequence, from two runs in the layout that satisfy `I` (what the first piece needs),
each piece leaving the layout. -/
theorem seqL {c₁ c₂ : Prog isa} {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, Lay D (sgR p) (sgW p) x → I x → WP isa c₁ x fun x' => (∃ W, PostB D x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.postDep h₁ (F := fun x x' => (∃ W, PostB D x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.lx h.2.1, w₁ y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hx hy, jx, jy⟩) h₂

theorem trL_mono {c : Prog isa} {I I' : State → Prop}
    (h : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) c fun _ _ => True) (hI : ∀ s, I' s → I s) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I' x ∧ I' y) c fun _ _ => True :=
  RelCT.mono h (fun _ _ h => ⟨h.1, hI _ h.2.1, hI _ h.2.2⟩) fun _ _ h => h

end

/-! ## Blocks -/

/-- Code that leaks only through the pointers of the layout (and the stack
pointer), as the taint analysis proves: for a block, by evaluation of
`checkBlock`, which does not look at offsets and immediates, so that they
may be variables. -/
theorem lrel_tr {S : Nat} {rbs wbs : List (Reg × Nat)} {P : State → State → Prop} {c : Prog isa}
    {hc : VG.Taint.Hint AArch64.Taint.T} (hr : ∀ x y, P x y → LRel S rbs wbs x y)
    (h : (taint.check (AArch64.Taint.ofRegs bases) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  taintRel bases (fun x y hp => ⟨(hr x y hp).sp, (hr x y hp).regs⟩) h

theorem vector_lrel_tr {S : Nat} {rbs wbs : List (Reg × Nat)} {P : State → State → Prop} {c : Prog isa}
    {hc : VG.Taint.Hint VectorTaint.T} (hr : ∀ x y, P x y → LRel S rbs wbs x y)
    (h : (VectorTaint.taint.check (VectorTaint.ofRegs bases) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  VectorTaint.relRegs bases (fun x y hp => ⟨(hr x y hp).sp, (hr x y hp).regs⟩) h

/-! ## `ρ` -/

theorem signLeakT_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeakT p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  unfold signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← skRho_eq p sk, e]
  subst hρ
  exact ⟨_, rfl⟩

theorem leak_rho {p : Params} {sk₁ sk₂ μ₁ μ₂ r₁ r₂ : List Byte} (h1 : sk₁.length = p.skLen)
    (h2 : sk₂.length = p.skLen) (h : signLeakT p sk₁ μ₁ r₁ = signLeakT p sk₂ μ₂ r₂) :
    sk₁.take 32 = sk₂.take 32 := by
  obtain ⟨X₁, e₁⟩ := signLeakT_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := signLeakT_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine leakBytes_inj (List.append_inj h ?_).1
  rw [leakBytes_length, leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {D : Nat} {σ₁ σ₂ : State} (h : (signK p D).pub σ₁ σ₂) :
    rhoOf p σ₁ = rhoOf p σ₂ :=
  leak_rho (VG.Proof.MlKem.bytesAt_length _ _ _) (VG.Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2

end VG.Proof.MlDsa.AArch64.Sign

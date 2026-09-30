import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr

/-!
# ML-DSA signing on x86-64: two runs

Untrusted: everything here is checked by Lean. Constant time is proven
piece by piece (`RelCT`) for two runs from entry states that satisfy
`signK`'s precondition and agree on its public data, each satisfying the
invariant `I` of the correctness proof, and related by `E` (`RR`): each
piece leaks the same, correctness gives each run's next invariant, and the
piece's own proof the next relation (`relInvE`). The runs are in the same
layout (`RR.lrel`) and agree on `ρ` (`RR.rho`), which the leakage begins
with.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Rel2)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (D : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  Rel2 (signK p D).pre (signK p D).pub I x y ∧ E x y

section
variable {p : Params} {D : Nat}

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
  have S₁ := hI _ _ i₁
  have S₂ := hI _ _ i₂
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun b hb => ?_, by rw [S₁.top.rsp, S₂.top.rsp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ (.rbp, .rdi) (by decide), r₂ (.rbp, .rdi) (by decide), h1]
  · rw [r₁ (.r12, .rsi) (by decide), r₂ (.r12, .rsi) (by decide), h2]
  · rw [r₁ (.r13, .rdx) (by decide), r₂ (.r13, .rdx) (by decide), h3]
  · rw [r₁ (.rbx, .r8) (by decide), r₂ (.rbx, .r8) (by decide), h5]
  · rw [r₁ (.r14, .rcx) (by decide), r₂ (.r14, .rcx) (by decide), h4]

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

end VG.Proof.MlDsa.X86_64.Sign

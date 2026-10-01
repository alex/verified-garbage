import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.CTAccess

/-! The signer's scalar and point operations keep all operand bytes secret. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed scalarReduce scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (rsp_ce)

theorem reduce_ct (out : Nat) (ho : out + 32 ≤ 128)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (reduceArgs out)) hint).isSome = true) :
    RelCT isa (Two fun _ _ _ => True) (reduce out) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block (reduceArgs out)) (Two fun L _ => ReduceArgs L out) :=
    two_blk ht fun _ _ _ _ _ _ hc _ => WP.mono (reduceArgs_ok hc ho)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := "vg_ed25519_scalar_reduce") (Φ := fun L _ => ReduceArgs L out)
    scalarReduce_ok scalarReduce_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    reduceRd (fun L => reduceWr L out) (fun _ _ _ _ _ hL hc ha => reduce_pre hL hc ha ho)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := reduce_regs a₁ (reduceRd L) (reduceWr L out)
      obtain ⟨d₂, s₂, x₂⟩ := reduce_regs a₂ (reduceRd L) (reduceWr L out)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (reduce_access out ho)
  exact b.seq c

theorem base_ct : RelCT isa (Two fun _ _ _ => True)
    (callWith baseArgs scalarBaseName scalarBase_precomputed) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block baseArgs) (Two fun L _ => BaseArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ => WP.mono (baseArgs_ok hc)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := scalarBaseName) (Φ := fun L _ => BaseArgs L)
    scalarBase_precomputed_ok scalarBase_precomputed_ct base_nosp base_depth baseRd baseWr
    (fun _ _ _ _ _ hL hc ha => base_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := base_regs a₁ (baseRd L) (baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := base_regs a₂ (baseRd L) (baseWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    base_access
  exact b.seq c

theorem mul_ct : RelCT isa (Two fun _ _ _ => True)
    (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block mulAddArgs) (Two fun L _ => MulArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ => WP.mono (mulArgs_ok hc)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := "vg_ed25519_scalar_mul_add") (Φ := fun L _ => MulArgs L)
    scalarMulAdd_ok scalarMulAdd_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    mulRd mulWr (fun _ _ _ _ _ hL hc ha => mul_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := mul_regs a₁ (mulRd L) (mulWr L)
      obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := mul_regs a₂ (mulRd L) (mulWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm,
        x₁.trans x₂.symm, k₁.trans k₂.symm, r₁.trans r₂.symm⟩) mul_access
  exact b.seq c

end VG.Proof.Ed25519.X86_64.SignCached

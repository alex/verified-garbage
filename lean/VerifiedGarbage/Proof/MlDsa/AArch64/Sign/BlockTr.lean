import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel

/-!
# ML-DSA signing on AArch64: blocks that leak only their pointers

Untrusted: everything here is checked by Lean. The taint analysis of a block
does not look at its offsets and immediates, so its check evaluates for code
in which they are variables (`setKappa_taint`); a copy's moves of its
addresses and length depend on their values only through the choice of
instructions (`copy_taint`), each of which leaves them public.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign

/-- The hint of a copy: its pointers and its counter are public in its loop. -/
abbrev copyHint : VG.Taint.Hint AArch64.Taint.T :=
  .seq (AArch64.Taint.ofRegs [.x0, .x1, .x2]) (.block []) (.loop (AArch64.Taint.ofRegs [.x0, .x1, .x2]) (.block []))

theorem copy_taint {b₁ b₂ : Reg} (h₁ : b₁ = .x28 ∨ b₁ = .x23) (h₂ : b₂ = .x28) (o₁ o₂ n : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (copy (b₁, o₁) (b₂, o₂) n) copyHint).isSome = true := by
  subst h₂
  rcases h₁ with rfl | rfl <;> dsimp only [copy, lea, movV] <;> (repeat' split) <;> rfl

theorem copy_tr {S : Nat} {rbs wbs : List (Reg × Nat)} {P : State → State → Prop} {b₁ b₂ : Reg}
    (h₁ : b₁ = .x28 ∨ b₁ = .x23) (h₂ : b₂ = .x28) {o₁ o₂ n : Nat} (hr : ∀ x y, P x y → LRel S rbs wbs x y) :
    RelCT isa P (copy (b₁, o₁) (b₂, o₂) n) fun _ _ => True :=
  lrel_tr hr (copy_taint h₁ h₂ o₁ o₂ n)

theorem setKappa_taint (r : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (setKappa r)) (.block [])).isSome = true := by
  dsimp only [setKappa]; rfl

end VG.Proof.MlDsa.AArch64.Sign

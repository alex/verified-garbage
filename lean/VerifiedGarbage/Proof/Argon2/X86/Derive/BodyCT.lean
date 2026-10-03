import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT3
import VerifiedGarbage.Proof.Argon2.X86.Derive.MemCT
import VerifiedGarbage.Proof.Argon2.X86.Derive.ReduceCT
import VerifiedGarbage.Proof.Argon2.X86.Derive.InitialCT
import VerifiedGarbage.Proof.Argon2.References

/-!
# Argon2 on x86 (32-bit): the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveX86.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frames.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- The parameters' block leaks the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)) fun _ _ => True := by
  rw [← List.singleton_append]
  refine RelCT.block_split (RelCT.seqW (F₁ := fun s => s = entry s₀₁) (F₂ := fun s => s = entry s₀₂)
    (RelCT.taint (A := taint) (τr [.esp]) (fun s₁ s₂ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2, entry_esp, entry_esp, T.pb.E]) (by taint_decide))
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i) ?_)
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.X86.Derive.body fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)
    (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  unfold Impl.Argon2.X86.Derive.body
  refine RelCT.seqW T.parameters_rel (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t)
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₁ fun t i p => WP.block_nil ⟨i, p⟩)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₂ fun t i p => WP.block_nil ⟨i, p⟩) ?_
  refine RelCT.seqW T.code_rel (fun s h => code_ok T.hp₁ h.1 h.2) (fun s h => code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (prm s₀₁)
      (Spec.Argon2.initialHash (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (prm s₀₂)
      (Spec.Argon2.initialHash (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
  exact T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end Two

/-- A frame around code related from the pushed states. -/
theorem frame_chain {P : State → State → Prop} {f : State → State} {rs : List Reg} {r : Reg} {k : Nat}
    {body : Prog isa} {Q : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → (f s₁).gpr .esp = (f s₂).gpr .esp)
    (h : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed rs (f s₁) ∧ b = pushed rs (f s₂)) body Q) :
    RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = f s₁ ∧ b = f s₂) (.frame (.push rs) body (.pop r k))
      fun _ _ => True :=
  RelCT.frame (fun a b ⟨s₁, s₂, hp, ha, hb⟩ => by subst ha hb; exact hsp s₁ s₂ hp)
    (h.mono (fun a b ⟨x, y, ⟨s₁, s₂, hp, hx, hy⟩, ha, hb⟩ => ⟨s₁, s₂, hp, by rw [ha, hx], by rw [hb, hy]⟩)
      fun _ _ h => h)

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => deriveX86.pre s₁ ∧ deriveX86.pre s₂ ∧ deriveX86.pub s₁ s₂)
      Impl.Argon2.X86.Derive.derive fun _ _ => True := by
  have esp : ∀ s₁ s₂ : State, s₁.gpr .esp = s₂.gpr .esp → ∀ rs : List Reg,
      (pushed rs s₁).gpr .esp = (pushed rs s₂).gpr .esp := fun s₁ s₂ h rs => by
    rw [pushed_esp, pushed_esp, h]
  refine (frame_chain (f := id) (fun s₁ s₂ h => h.2.2.1.1) (frame_chain (f := fun s => pushed [.ebp] s)
    (fun s₁ s₂ h => esp _ _ h.2.2.1.1 _) (frame_chain (f := fun s => pushed [.edi] (pushed [.ebp] s))
    (fun s₁ s₂ h => esp _ _ (esp _ _ h.2.2.1.1 _) _)
    (frame_chain (f := fun s => pushed [.esi] (pushed [.edi] (pushed [.ebp] s)))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _)
    (frame_chain (Q := fun _ _ => True) (f := fun s => pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s))))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _) _) ?_))))).mono
    (fun s₁ s₂ h => ⟨s₁, s₂, h, rfl, rfl⟩) fun _ _ h => h
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, ha, hb⟩ e₁ e₂
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 a b t₁ t₂ a' b' ⟨ha, hb⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveX86.pre deriveX86.pub Impl.Argon2.X86.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.X86.Derive

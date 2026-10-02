import VerifiedGarbage.Proof.AesGcm.Arm.CTJ0

/-!
# AES-GCM on ARMv7: constant time of the functions, the tools

Untrusted: everything here is checked by Lean. The functions relate two runs
from initial states `s₀` and `s₀'` with the same public data (`F`, `F'`
describe each run from its initial state); the pieces' `CT` lemmas apply
with the public data of `s₀` (`rel_of_ct`); blocks that read stack
arguments are checked with them public (`rel_argTaint`), from `ArgsKeep`.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem rel_of_ct {I F F' : State → Prop} {c : Prog isa} (h : CT I c) (h₁ : ∀ s, F s → I s)
    (h₂ : ∀ s, F' s → I s) : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True :=
  RelCT.mono h (fun _ _ hh => ⟨h₁ _ hh.1, h₂ _ hh.2⟩) fun _ _ _ => trivial

/-- The stack arguments, as public in the taint analysis, from two runs that keep them. -/
theorem ArgsKeep.agree {n : Nat} {s₀ s₀' s s' : State} (hk : ArgsKeep n s₀ s) (hk' : ArgsKeep n s₀' s')
    (hsp : s₀.sp = s₀'.sp) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32) (ha : ∀ i < n, stackArg s₀ i = stackArg s₀' i)
    (hw : ∀ r ∈ s₀.wr, (args s₀ n).Disjoint r) (hw' : ∀ r ∈ s₀'.wr, (args s₀' n).Disjoint r)
    {rs : List Reg} (hr : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    VG.Arm.Taint.Agree (argTaint rs (4 * n)) s s' := by
  have e : ∀ {t₀ t : State}, ArgsKeep n t₀ t → (∀ r ∈ t₀.wr, (args t₀ n).Disjoint r) →
      t.sp.toNat + 4 * n ≤ 2 ^ 32 → t.sp.toNat + 4 * n ≤ 2 ^ 32 ∧
        ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4 * n⟩ r := fun {t₀ t} k w f => by
    refine ⟨f, fun r hr => ?_⟩
    rw [k.wr] at hr
    have := w r hr
    simp only [args, argAddr_zero] at this
    rwa [← k.sp] at this
  have f : s.sp.toNat + 4 * n ≤ 2 ^ 32 := by rw [hk.sp]; exact hf
  have f' : s'.sp.toNat + 4 * n ≤ 2 ^ 32 := by rw [hk'.sp, ← hsp]; exact hf
  have hsp' : s.sp = s'.sp := by rw [hk.sp, hk'.sp, hsp]
  exact agree_argTaint hr hsp' (e hk hw f) (e hk' hw' f')
    (argMem_of hsp' f fun i hi => by rw [hk.arg i hi, hk'.arg i hi, ha i hi])

theorem ArgsKeep.weaken {n m : Nat} {s₀ s : State} (h : ArgsKeep n s₀ s) (hm : m ≤ n) : ArgsKeep m s₀ s :=
  ⟨h.sp, h.rd, h.wr, fun i hi => h.arg i (by omega)⟩

theorem args_sub (s : State) {m n : Nat} (hm : m ≤ n) : Region.Sub (args s m) (args s n) :=
  Region.sub_prefix (by omega)

theorem rel_ite {F F' : State → Prop} {t e : Prog isa} (b : Bool) (hz : ∀ s, F s → s.z = b)
    (hz' : ∀ s, F' s → s.z = b) (ht : b = true → RelCT isa (fun a b => F a ∧ F' b) t fun _ _ => True)
    (he : b = false → RelCT isa (fun a b => F a ∧ F' b) e fun _ _ => True) :
    RelCT isa (fun a b => F a ∧ F' b) (.ite .eq t e) fun _ _ => True := by
  refine RelCT.ite (fun _ _ h => by rw [eval_eq' (hz _ h.1), eval_eq' (hz' _ h.2)]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

theorem rel_skip {F F' : State → Prop} : RelCT isa (fun a b => F a ∧ F' b) (.block []) fun _ _ => True :=
  rel_of_ct (I := fun _ => True) CT.skip (fun _ _ => trivial) (fun _ _ => trivial)

end VG.Proof.AesGcm.Arm

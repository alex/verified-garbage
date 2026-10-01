import VerifiedGarbage.Proof.Rc2.X86_64.Rounds

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), Words s v →
      (ScanMemory s) →
      WP isa (.block (code i)) s (fun s' =>
        Words s' (step (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) ∧ Keep roundWrites s s'))
    (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (readable : ScanMemory s) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      Words s' (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) v) ∧
      Keep roundWrites s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv readable)
    intro s₁ h₁
    have ptr₁ := h₁.2.reg .rdi (by decide)
    have read₁ : ScanMemory s₁ := readable.keep h₁.2 (by decide) (by decide)
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 read₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.mem, ptr₁] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (readable : ScanMemory s) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound := List.mem_range.mp hi
  apply WP.mono (mix_ok s v hv i (4 * j + i) bound (by omega) readable.bytes)
  exact fun _ h => ⟨h.1, h.2.round⟩

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (readable : ScanMemory s) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  apply WP.mono (reverseMix_ok s v hv i (4 * j + i) bound (by omega) readable.bytes)
  exact fun _ h => ⟨h.1, h.2.round⟩

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (readable : ScanMemory s) :
    WP isa (.block ((order d).flatMap (mash d))) s (fun s' =>
      Words s' (mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) v) ∧
      Keep roundWrites s s') := by
  have he (k : Spec.Rc2.Schedule) : mashRoundSpec d k v =
      (order d).foldl (fun v i => mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply foldWords_ok (step := fun k i v => mashSpec d k i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  apply WP.mono (mash_ok d s v hv i bound readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (readable : ScanMemory s) :
    WP isa (.block (round d j)) s (fun s' =>
      Words s' (roundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep roundWrites s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : Words s₁ v₁ ∧ Keep roundWrites s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        Words s₂ (if j = 4 ∨ j = 10 then mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) v₁
          else v₁) ∧ Keep roundWrites s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      have ptr₁ := h₁.2.reg .rdi (by decide)
      have read₁ : ScanMemory s₁ := readable.keep h₁.2 (by decide) (by decide)
      apply WP.mono (mashRound_ok d s₁ v₁ h₁.1 read₁)
      intro s₂ h₂
      rw [h₁.2.mem, ptr₁] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (mixRound_ok s v hv j hj readable)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (reverseMixRound_ok s v hv (15 - j) (by omega) readable)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (readable : ScanMemory s) :
    WP isa (.block ((List.range 16).flatMap (round d))) s (fun s' =>
      Words s' ((List.range 16).foldl (fun v j => roundSpec d
        (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) v) ∧ Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k j v => roundSpec d k j v) _ _ _ s v hv readable
  intro j hj s v hv readable
  exact round_ok d s v hv j (List.mem_range.mp hj) readable

end VG.Proof.Rc2.X86_64

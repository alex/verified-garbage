import VerifiedGarbage.Proof.AesGcm.Arm.CTFn
import VerifiedGarbage.Proof.AesGcm.Arm.StreamAad

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem streamInit_rel {s₀ s₀' : State} (h0 : streamInitArm.pre s₀) (h0' : streamInitArm.pre s₀')
    (hq : streamInitArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamInit fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅⟩ := hq
  have L := siLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw : ∀ {t : State}, streamInitArm.pre t → ∀ r ∈ t.wr, (args t 1).Disjoint r := fun {t} ht r hr => by
    obtain ⟨-, hwr, -, -, -, -, -, dsA, dWA, -⟩ := ht
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsA.symm
    · exact dWA.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] (4 * 1)) (.block streamInitPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SI1 s₀) (G' := SI1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 1)) (c := .block streamInitPre)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 1 s).agree (ArgsKeep.refl 1 s') q₀ spf (fun i hi => by
        obtain rfl : i = 0 := by omega
        exact q₅) (hw h0) (hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact si1_wp h0) (fun s e => by rw [e]; exact si1_wp h0')
  have hlt := (s₀.gpr .r2).isLt
  have b := rel_wp (F := SI1 s₀) (F' := SI1 s₀') (G := SI2 s₀) (G' := SI2 s₀')
    (rel_of_ct (j0_ct L (Np := s₀.gpr .r1) (n := (s₀.gpr .r2).toNat) hlt) (fun s h1 => ⟨_, _, _, si_j0In h0 h1⟩)
      (fun s h1 => by
        have := si_j0In h0' h1
        rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₀] at this
        exact ⟨_, _, _, this⟩))
    (fun s h1 => WP.mono (j0_ok (siLay h0) (si_j0In h0 h1)) fun s' ho => ⟨s, h1, ho⟩)
    (fun s h1 => WP.mono (j0_ok (siLay h0') (si_j0In h0' h1)) fun s' ho => ⟨s, h1, ho⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have c := RelCT.taint (A := taint) (P := fun s₁ s₂ => SI2 s₀ s₁ ∧ SI2 s₀' s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨_, e₁⟩ := h₁.env; obtain ⟨_, e₂⟩ := h₂.env
      rw [e₁.r11, e₂.r11, q₅]) hB
  exact a.seq (b.seq c)

theorem streamInit_ct : ConstantTime isa streamInitArm.pre streamInitArm.pub streamInit :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamInit_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem streamAad_rel {s₀ s₀' : State} (h0 : streamAadArm.pre s₀) (h0' : streamAadArm.pre s₀')
    (hq : streamAadArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamAad fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have L := saLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw : ∀ {t : State}, streamAadArm.pre t → ∀ r ∈ t.wr, (args t 3).Disjoint r := fun {t} ht r hr => by
    obtain ⟨-, hwr, -, -, -, -, -, dsA, dWA, -⟩ := ht
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsA.symm
    · exact dWA.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] (4 * 3)) (.block streamAadPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SA1 s₀) (G' := SA1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 3)) (c := .block streamAadPre)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 3 s).agree (ArgsKeep.refl 3 s') q₀ spf (fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · exact q₅
        · exact q₆
        · exact q₇) (hw h0) (hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact sa1_wp h0) (fun s e => by rw [e]; exact sa1_wp h0')
  have b := rel_wp (F := SA1 s₀) (F' := SA1 s₀') (G := fun s => ∃ x, SA2 s₀ x s) (G' := fun s => ∃ x, SA2 s₀' x s)
    (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 0) (n := (arg s₀ 1).toNat)
      (q := (s₀.gpr .r2).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s h1 => ⟨_, _, _, _, by simp, sa_absIn h0 h1 (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0) (by simp)⟩)
      (fun s h1 => by
        have := sa_absIn h0' h1 (x := List.replicate ((s₀'.gpr .r2).toNat % 16) 0) (by simp)
        rw [← q₁, ← q₂, ← q₃, ← q₅, ← q₆, ← q₇, ← q₀] at this
        exact ⟨_, _, _, _, by simp, this⟩))
    (fun s h1 => WP.mono (absorb_ok L (.inr rfl) (sa_absIn h0 h1 (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0)
      (by simp))) fun s' ho => ⟨_, s, h1, ho⟩)
    (fun s h1 => WP.mono (absorb_ok (saLay h0') (.inr rfl) (sa_absIn h0' h1
      (x := List.replicate ((s₀'.gpr .r2).toNat % 16) 0) (by simp))) fun s' ho => ⟨_, s, h1, ho⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have c := RelCT.taint (A := taint) (P := fun s₁ s₂ => (∃ x, SA2 s₀ x s₁) ∧ ∃ x, SA2 s₀' x s₂)
    (c := .block restore) (Taint.ofRegs [.r11]) (fun s₁ s₂ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩⟩ =>
      Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h₁.env.r11, h₂.env.r11, q₇]) hB
  exact a.seq (b.seq c)

theorem streamAad_ct : ConstantTime isa streamAadArm.pre streamAadArm.pub streamAad :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamAad_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

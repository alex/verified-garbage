import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.CTCommon

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

variable {s₁ s₂ : State}

theorem init_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots initValues))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : initValues.length ≤ 6) (by simp [initValues, Whole.valid])
    (Proof.Sha512.X86.Stream.init_verified _).1 (Proof.Sha512.X86.Stream.init_verified _).2.1
    Whole.init_nosp (by rw [Whole.init_stack]; decide) init_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj 0 (by decide)⟩

theorem update_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots updateValues)) (.call Spec.Sha512.updateApi.name Impl.Sha512.X86.Stream.update)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : updateValues.length ≤ 6) (by simp [updateValues, Whole.valid])
    Proof.Sha512.X86.Stream.Update.update_verified.1 Proof.Sha512.X86.Stream.Update.update_verified.2.1
    Whole.update_nosp (by rw [Whole.update_stack]) update_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj⟩

theorem finalize_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots finalizeValues)) (.call Spec.Sha512.finalizeApi.name Impl.Sha512.X86.Stream.finalize)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : finalizeValues.length ≤ 6) (by simp [finalizeValues, Whole.valid])
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.1 Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1
    Whole.finalize_nosp (by rw [Whole.finalize_stack]) finalize_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj⟩

theorem base_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots baseValues)) (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : baseValues.length ≤ 6) (by simp [baseValues, Whole.valid])
    scalarBase_ok scalarBase_ct base_nosp (by rw [base_stack]; decide) base_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj 0 (by decide), hj 1 (by decide), hj 2 (by decide)⟩

theorem prune_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) (.block prune) (Two s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (prune_step h hc (digest := Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64) rfl)
    fun _ hu => ⟨hu.1, trivial⟩

theorem wipe_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) (.block wipe) (Two s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega) (by decide)) fun _ hu => ⟨hu.1, trivial⟩

theorem body_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) body (Two s₁ s₂ fun _ _ => True) := by
  have i := setup_ct h₁ h₂ pub initValues (by decide) (by simp [initValues, Whole.valid]) (by taint_decide)
  have u := setup_ct h₁ h₂ pub updateValues (by decide) (by simp [updateValues, Whole.valid]) (by taint_decide)
  have f := setup_ct h₁ h₂ pub finalizeValues (by decide) (by simp [finalizeValues, Whole.valid]) (by taint_decide)
  have b := setup_ct h₁ h₂ pub baseValues (by decide) (by simp [baseValues, Whole.valid]) (by taint_decide)
  exact ((i.seq (init_ct h₁ h₂ pub)).seq
    ((u.seq (update_ct h₁ h₂ pub)).seq (f.seq (finalize_ct h₁ h₂ pub)))).seq
    ((prune_ct h₁ h₂ pub).seq ((b.seq (base_ct h₁ h₂ pub)).seq (wipe_ct h₁ h₂ pub)))

theorem publicKey_ct : ConstantTime isa pkLocal.pre pkLocal.pub publicKey := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  exact ⟨(body_ct (facts p₁) (facts p₂) hp _ _ _ _ _ _
    ⟨push_ctx p₁, push_ctx p₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.PublicKey

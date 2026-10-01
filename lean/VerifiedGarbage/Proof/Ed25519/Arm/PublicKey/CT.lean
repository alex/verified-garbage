import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.CTReady
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.PruneCT

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L initValues []))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512)) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl (fun _ _ h => init_ready hL h)
  · intro a b ar aw br bw hsp hg ht
    exact hg (.r0, .caller 2 0) (by simp [initValues])
  · simp [initValues, linkRegs]

theorem update_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L updateValues updateStack))
    (.call Spec.Sha512.updateApi.name Impl.Sha512.Arm.Stream.update) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1 Proof.Sha512.Arm.Stream.Update.update_verified.2.1
    Whole.update_noFrames (fun _ he h => update_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [updateValues]), hg (.r2, .const 0) (by simp [updateValues]), hg (.r3, .const 0) (by simp [updateValues]), ht 0 (by decide), ht 1 (by decide), ht 2 (by decide)⟩
  · simp [updateValues, linkRegs]

theorem finalize_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L finalizeValues finalizeStack))
    (.call Spec.Sha512.finalizeApi.name Impl.Sha512.Arm.Stream.finalize) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1 Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1
    Whole.finalize_noFrames (fun _ he h => finalize_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [finalizeValues]), hg (.r2, .const 32) (by simp [finalizeValues]), hg (.r3, .const 0) (by simp [finalizeValues]), ht 0 (by decide), ht 1 (by decide)⟩
  · simp [finalizeValues, linkRegs]

theorem base_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L baseValues []))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarBase_ok scalarBase_ct base_noFrames (fun _ _ h => base_ready hL h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 0 0) (by simp [baseValues]), hg (.r1, .frame 24) (by simp [baseValues]), hg (.r2, .caller 2 0) (by simp [baseValues])⟩
  · simp [baseValues, linkRegs]

theorem prune_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 6 56).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have i := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb initValues []
    (by decide) (by simp [initValues, Whole.valid]) (by simp [initValues])
    (by simp [initValues, preserved]) (by decide) (by simp [Whole.valid])
    (by simp)
  have u := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb updateValues updateStack
    (by decide) (by simp [updateValues, Whole.valid]) (by simp [updateValues])
    (by simp [updateValues, preserved]) (by decide) (by simp [updateStack, Whole.valid])
    (by simp [updateStack])
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb finalizeValues finalizeStack
    (by decide) (by simp [finalizeValues, Whole.valid]) (by simp [finalizeValues])
    (by simp [finalizeValues, preserved]) (by decide) (by simp [finalizeStack, Whole.valid])
    (by simp [finalizeStack])
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb baseValues []
    (by decide) (by simp [baseValues, Whole.valid]) (by simp [baseValues])
    (by simp [baseValues, preserved]) (by decide) (by simp [Whole.valid])
    (by simp)
  exact ((i.seq (init_ct hL)).seq ((u.seq (update_ct hL)).seq (f.seq (finalize_ct hL)))).seq
    ((prune_ct hL).seq ((b.seq (base_ct hL)).seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2]

theorem publicKey_ct : ConstantTime isa pkLocal.pre pkLocal.pub code := by
  refine Whole.wrap_ct (by decide : 3 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) ?_ (by intro s hs j hj h4; omega) ?_ ?_
  · intro s _
    simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt s.sp.isLt
  · intro s hs p hp
    exact WP.mono (body_ok (entry_ctx hs hp) (lay_ok hs) (entry_args (entry_below hs) hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args (entry_below ht) hqb
    exact ⟨(body_ct (lay_ok hs) (entry_args (entry_below hs) hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.Arm.PublicKey

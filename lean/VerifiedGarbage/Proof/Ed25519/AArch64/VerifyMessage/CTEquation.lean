import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTReady

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem equation_setup_wp {g v m t} (hc : Ctx L g v m t) (hL : L.Ok) (ha : Arguments L m)
    {ch : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = ch) :
    WP isa (.block VerifyMessage.equationArgs) t fun u => Ctx L g v m u ∧ EqArgs L u ∧
      Spec.Ed25519.bytesAt u.mem (L.E + 128) 64 = ch := by
  refine WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 0 0),(.x1,.caller 3 0),(.x2,.frame 128),(.x3,.caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [known]) (by simp [preserved])) ?_
  intro u ⟨hu,hm,hav⟩
  have a0 := hav (.x0,.caller 0 0) (by simp)
  have a1 := hav (.x1,.caller 3 0) (by simp)
  have a2 := hav (.x2,.frame 128) (by simp)
  have a3 := hav (.x3,.caller 4 0) (by simp)
  change u.gpr .x0 = L.pk+0#64 at a0
  change u.gpr .x1 = L.sig+0#64 at a1
  change u.gpr .x3 = L.scr+0#64 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  exact ⟨hu,⟨a0,a1,a2,a3⟩,hm ▸ hh⟩

theorem equation_call_ct (hL : L.Ok) {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => EqArgs L t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (.call "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct verify_ok verify_ct (Whole.depth_of_noFrames equation_noFrames) (fun _ h => equation_ready hL h.1)
  intro a b ar aw br bw h
  have hsp := two_sp h
  have aa := h.2.2.1.1
  have ab := h.2.2.2.1
  have pk₁ := Ctx.input_bytes h.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have pk₂ := Ctx.input_bytes h.2.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have sig₁ := Ctx.input_bytes h.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  have sig₂ := Ctx.input_bytes h.2.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  simp only [verifyLocal, State.withRegions_gpr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    aa.1, aa.2.1, aa.2.2.1, aa.2.2.2, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2]
  exact ⟨hsp,trivial,trivial,trivial,trivial,pk₁.trans (hpk.trans pk₂.symm),
    sig₁.trans (hsig.trans sig₂.symm),h.2.2.1.2.trans h.2.2.2.2.symm⟩

theorem equation_step_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (Whole.callWith VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hs : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (.block VerifyMessage.equationArgs)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => EqArgs L t ∧ Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge) := by
    apply two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide))
    · intro t hc hh
      exact equation_setup_wp hc hL ha hh
    · intro t hc hh
      exact equation_setup_wp hc hL hb hh
  exact hs.seq (equation_call_ct hL hpk hsig)

end VG.Proof.Ed25519.AArch64.VerifyMessage

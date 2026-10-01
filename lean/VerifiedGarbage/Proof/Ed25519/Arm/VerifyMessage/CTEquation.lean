import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTReady

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem equation_setup_wp {g m t} (hc : Ctx L g m t) (hL : L.Ok) (ha : Arguments L m)
    {ch : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = ch) :
    WP isa (.block VerifyMessage.equationArgs) t fun u => Ctx L g m u ∧ EqArgs L u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 120) 64 = ch := by
  refine WP.mono (args_regs_ok hc hL ha
    (args := [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)])
    (by simp) (by simp [valid]) (by simp [preserved])) ?_
  intro u ⟨hu,hm,hav⟩
  have a0 := hav (.r0,.caller 0 0) (by simp)
  have a1 := hav (.r1,.caller 3 0) (by simp)
  have a2 := hav (.r2,.frame 120) (by simp)
  have a3 := hav (.r3,.caller 4 0) (by simp)
  change u.gpr .r0 = L.pk+0#32 at a0
  change u.gpr .r1 = L.sig+0#32 at a1
  change u.gpr .r3 = L.scr+0#32 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  exact ⟨hu,⟨a0,a1,a2,a3⟩,hm ▸ hh⟩

theorem equation_call_ct (hL : L.Ok) {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64 = Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => EqArgs L t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (.call "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct verify_ok verify_ct equation_noFrames (fun _ h => equation_ready hL h.1)
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
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    aa.1, aa.2.1, aa.2.2.1, aa.2.2.2, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2]
  have ac : State.addr (L.E+120) = State.addr L.E+120 := frame_addr hL (d := 120) (by decide)
  rw [ac]
  refine ⟨hsp,trivial,trivial,trivial,trivial,?_⟩
  have kp := pk₁.trans (hpk.trans pk₂.symm)
  have ks := sig₁.trans (hsig.trans sig₂.symm)
  have kh := h.2.2.1.2.trans h.2.2.2.2.symm
  change Spec.Ed25519.bytesAt a.mem (State.addr L.pk) 32 = Spec.Ed25519.bytesAt b.mem (State.addr L.pk) 32 at kp
  change Spec.Ed25519.bytesAt a.mem (State.addr L.sig) 64 = Spec.Ed25519.bytesAt b.mem (State.addr L.sig) 64 at ks
  rw [kp,ks,kh]

theorem equation_step_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64 = Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (Whole.callWith VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs : RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (.block VerifyMessage.equationArgs)
      (Two L g₁ g₂ m₁ m₂ fun t => EqArgs L t ∧ Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge) := by
    apply two_wp ((Whole.setup_ct
      [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)] []).mono
      (fun _ _ h => two_sp h) (fun _ _ _ => True.intro))
    · intro t hc hh
      exact equation_setup_wp hc hL ha hh
    · intro t hc hh
      exact equation_setup_wp hc hL hb hh
  exact hs.seq (equation_call_ct hL hpk hsig)

end VG.Proof.Ed25519.Arm.VerifyMessage

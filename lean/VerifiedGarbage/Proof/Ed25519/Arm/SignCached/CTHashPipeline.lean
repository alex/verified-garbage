import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTHash

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem hashSeed_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (hashSeed)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hi : Input L (value L (.caller 1 0)) (value L (.const 32)) := by
    change Input L (L.seed + 0#32) 32#32
    rw [BitVec.add_zero]
    exact seed_input hL
  exact (init_ct hL ha hb).seq ((update_ct hL ha hb 0 (.caller 1 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hi).seq
    (finalize_ct hL ha hb 32 (by decide) false))

theorem hashNonce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (hashNonce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hp : Input L (value L (.frame 56)) (value L (.const 32)) := prefix_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#32) (L.len + 0#32)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct hL ha hb 0 (.frame 56) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hp).seq
    ((update_ct hL ha hb 32 (.caller 3 0) (.caller 4 0)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm).seq
      (finalize_ct hL ha hb 32 (by decide) true)))

theorem hashChallenge_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (hashChallenge)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ho : Input L (value L (.caller 0 0)) (value L (.const 32)) := by
    change Input L (L.out + 0#32) 32#32
    rw [BitVec.add_zero]
    exact point_input hL
  have hk : Input L (value L (.caller 2 0)) (value L (.const 32)) := by
    change Input L (L.pk + 0#32) 32#32
    rw [BitVec.add_zero]
    exact key_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#32) (L.len + 0#32)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct hL ha hb 0 (.caller 0 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) ho).seq
    ((update_ct hL ha hb 32 (.caller 2 0) (.const 32)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hk).seq
      ((update_ct hL ha hb 64 (.caller 3 0) (.caller 4 0)
        (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm).seq
        (finalize_ct hL ha hb 64 (by decide) true))))

end VG.Proof.Ed25519.Arm.SignCached

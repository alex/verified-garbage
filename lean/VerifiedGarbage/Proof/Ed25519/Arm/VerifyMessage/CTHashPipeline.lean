import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTHash

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem prefix_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (source count : Nat) (hj : source < 5) (hc : count < 65536) (hi : Input L (L.value source) 32) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (update (prefixArgs source count))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have inp : Input L (value L (.caller source 0)) (value L (.const 32)) := by
    change Input L (L.value source+0#32) 32#32
    rw [BitVec.add_zero]
    exact hi
  exact update_ct hL ha hb count (.caller source 0) (.const 32) hc ⟨hj,by decide⟩ (by simp [valid]) inp

theorem message_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (update (messageArgs 64))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have inp : Input L (value L (.caller 1 0)) (value L (.caller 2 0)) := by
    simpa only [value,Lay.value,BitVec.add_zero] using message_input hL
  exact update_ct hL ha hb 64 (.caller 1 0) (.caller 2 0) (by decide)
    (by simp [valid]) (by simp [valid]) inp

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) VG.Impl.Ed25519.Arm.VerifyMessage.hash
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (init_ct hL ha hb).seq ((prefix_ct hL ha hb 3 0 (by decide) (by decide) (signature_input hL)).seq
    ((prefix_ct hL ha hb 0 32 (by decide) (by decide) (key_input hL)).seq
      ((message_ct hL ha hb).seq (finalize_ct hL ha hb 64 (by decide) true))))

end VG.Proof.Ed25519.Arm.VerifyMessage

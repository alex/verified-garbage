import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTHashPipeline
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTScalars
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTEquation

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem hash_result_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hm : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) VG.Impl.Ed25519.Arm.VerifyMessage.hash
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact hash_ok hc hL ha
  · intro t hc _
    refine WP.mono (hash_ok hc hL hb) fun u ⟨hu,hh⟩ => ⟨hu,?_⟩
    rw [hm]
    exact hh

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32=Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hmsg : Spec.Ed25519.bytesAt m₁ (State.addr L.msg) L.len.toNat=Spec.Ed25519.bytesAt m₂ (State.addr L.msg) L.len.toNat)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64=Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hm : hashInput L m₁=hashInput L m₂ := by
    rw [hashInput_eq,hashInput_eq,hpk,hmsg,hsig]
  exact (hash_result_ct hL ha hb hm).seq
    ((reduce_ct hL ha hb _).seq ((extend_ct hL _).seq (equation_step_ct hL ha hb hpk hsig)))

end VG.Proof.Ed25519.Arm.VerifyMessage

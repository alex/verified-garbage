import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.CTEquation
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Correct

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hp : Spec.Ed25519.bytesAt m₁ (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₂ (L.pk.setWidth 64) 32)
    (hm : Spec.Ed25519.bytesAt m₁ (L.msg.setWidth 64) L.len.toNat =
      Spec.Ed25519.bytesAt m₂ (L.msg.setWidth 64) L.len.toNat)
    (hs : Spec.Ed25519.bytesAt m₁ (L.sig.setWidth 64) 64 = Spec.Ed25519.bytesAt m₂ (L.sig.setWidth 64) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hi : hashInput L m₁ = hashInput L m₂ := by
    rw [hashInput_eq, hashInput_eq, hp, hm, hs]
  exact (hash_ct_result hL ha hb hi).seq ((reduce_ct hL ha hb _).seq
    ((extend_ct hL _).seq ((equation_setup_ct hL ha hb _).seq (equation_call_ct hL _ hp hs))))

theorem verifyMessage_ct : ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub code := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  obtain ⟨esp, a0, a1, a2, a3, a4, pk, msg, sig⟩ := hp
  have eqL : lay s₁ = lay s₂ := by simp only [lay, esp, a0, a1, a2, a3, a4]
  have h₂ : Ctx (lay s₁) s₂.gpr s₂.mem (pushed (List.replicate 64 .eax) s₂) := eqL.symm ▸ push_ctx p₂
  have arg₂ : Arguments (lay s₁) s₂.mem := eqL.symm ▸ lay_arguments p₂
  have pk' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).pk.setWidth 64) 32 =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).pk.setWidth 64) 32 := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 0).setWidth 64) 32 = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 0).setWidth 64) 32
    rw [← a0] at pk
    with_reducible exact pk
  have msg' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).msg.setWidth 64) (lay s₁).len.toNat =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).msg.setWidth 64) (lay s₁).len.toNat := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 1).setWidth 64) (arg s₁ 2).toNat = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 1).setWidth 64) (arg s₁ 2).toNat
    rw [← a1, ← a2] at msg
    with_reducible exact msg
  have sig' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).sig.setWidth 64) 64 =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).sig.setWidth 64) 64 := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 3).setWidth 64) 64 = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 3).setWidth 64) 64
    rw [← a3] at sig
    with_reducible exact sig
  exact ⟨(body_ct (lay_ok p₁) (lay_arguments p₁) arg₂ pk' msg' sig' _ _ _ _ _ _
    ⟨push_ctx p₁, h₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.VerifyMessage

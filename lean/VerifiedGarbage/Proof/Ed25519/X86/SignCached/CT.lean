import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTBody
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Correct

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

theorem lay_eq {s t : State} (h : signCachedLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, a0, a1, a2, a3, a4, a5⟩ := h
  simp only [lay, sp, a0, a1, a2, a3, a4, a5]

theorem signCached_ct : ConstantTime isa signCachedLocal.pre signCachedLocal.pub code := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have he := lay_eq hp
  have h₂ : Ctx (lay s₁) s₂.gpr s₂.mem (pushed (List.replicate 64 .eax) s₂) :=
    he ▸ push_ctx p₂
  have ha₂ : Arguments (lay s₁) s₂.mem := he ▸ lay_arguments p₂
  exact ⟨(body_ct (lay_ok p₁) (lay_arguments p₁) ha₂ _ _ _ _ _ _
    ⟨push_ctx p₁, h₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached

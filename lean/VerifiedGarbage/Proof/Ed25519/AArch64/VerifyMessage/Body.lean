import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.HashPipeline
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Challenge
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Equation

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
    (Spec.Ed25519.bytesAt m L.sig 64).take 32 ++
      Spec.Ed25519.bytesAt m L.pk 32 ++
      Spec.Ed25519.bytesAt m L.msg L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m L.sig 64).take 32 =
      Spec.Ed25519.bytesAt m L.sig 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem body_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) :
    WP isa (body backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verify (Spec.Ed25519.bytesAt m₀ L.pk 32)
        (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) (Spec.Ed25519.bytesAt m₀ L.sig 64)) := by
  refine WP.seq (WP.mono (hash_ok backend hc hL ha) fun t ⟨ht,hh⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step ht hL ha) fun u ⟨hu,_,hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (extend_step hu hr) fun w ⟨hw,he⟩ => ?_)
  rw [hashInput_eq] at he
  refine WP.mono (equation_step hw hL ha) fun z ⟨hz,eq⟩ => ⟨hz,?_⟩
  rw [hw.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide),
    hw.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64≤2^64; decide),he] at eq
  exact eq

theorem body_noFrames (backend : Whole.Backend) : (body backend.code backend.suffix).noFrames = true := by
  have hu := Whole.update_noFrames backend
  have hf := Whole.finalize_noFrames backend
  change (Impl.Sha512.AArch64.Stream.updateWith backend.code).noFrames = true at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith backend.code).noFrames = true at hf
  simp only [body,Impl.Ed25519.AArch64.VerifyMessage.hash,init,update,finalize,Impl.Ed25519.AArch64.Whole.callWith,
    Code.noFrames,Impl.Sha512.AArch64.Stream.init,hu,hf,Bool.and_self]
  rw [reduce_noFrames,equation_noFrames]
  rfl

end VG.Proof.Ed25519.AArch64.VerifyMessage

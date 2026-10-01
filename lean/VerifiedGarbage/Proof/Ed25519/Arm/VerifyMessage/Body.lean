import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.HashPipeline
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Challenge
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Equation

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
    (Spec.Ed25519.bytesAt m (State.addr L.sig) 64).take 32 ++
      Spec.Ed25519.bytesAt m (State.addr L.pk) 32 ++
      Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m (State.addr L.sig) 64).take 32 =
      Spec.Ed25519.bytesAt m (State.addr L.sig) 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) :
    WP isa body s fun t => Ctx L g m₀ t ∧
      t.gpr .r0 = signWord (Spec.Ed25519.verify (Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) (Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 64)) := by
  refine WP.seq (WP.mono (hash_ok hc hL ha) fun t ⟨ht,hh⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step ht hL ha) fun u ⟨hu,_,hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (extend_step hu hL hr) fun w ⟨hw,he⟩ => ?_)
  rw [hashInput_eq] at he
  refine WP.mono (equation_step hw hL ha) fun z ⟨hz,eq⟩ => ⟨hz,?_⟩
  rw [hw.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide),
    hw.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64≤2^64; decide),he] at eq
  exact eq

theorem body_noFrames : body.noFrames = true := by
  have hu := Whole.update_noFrames
  have hf := Whole.finalize_noFrames
  simp only [body,Impl.Ed25519.Arm.VerifyMessage.hash,init,update,finalize,Impl.Ed25519.Arm.Whole.callWith,
    Code.noFrames,Impl.Sha512.Arm.Stream.init,hu,hf,Bool.and_self]
  rw [reduce_noFrames,equation_noFrames]
  rfl

end VG.Proof.Ed25519.Arm.VerifyMessage

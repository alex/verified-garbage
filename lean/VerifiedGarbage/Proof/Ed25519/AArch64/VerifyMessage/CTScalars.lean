import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTReady

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def reduceValues : List (Reg × Value) := [(.x0,.frame 128),(.x1,.frame 192),(.x2,.caller 4 0)]

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L reduceValues))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0,.frame 128) (by simp [reduceValues])
    have a1 := hs (.x1,.frame 192) (by simp [reduceValues])
    have a2 := hs (.x2,.caller 4 0) (by simp [reduceValues])
    change t.gpr .x2=L.scr+0#64 at a2
    exact reduce_ready hL ⟨a0,a1,a2.trans (BitVec.add_zero _)⟩
  · intro a b ar aw br bw h
    simp only [scalarReduceLocal,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨two_sp h,call_gpr_eq h (p := (.x0,.frame 128)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.x1,.frame 192)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.x2,.caller 4 0)) (by simp [reduceValues]) (by decide)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64=digest)
      (callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest) := by
  have hs := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb reduceValues
    (by decide) (by simp [reduceValues,Whole.valid]) (by simp [reduceValues,known])
    (by simp [reduceValues,preserved]) (by taint_decide)
  refine two_wp ((hs.seq (reduce_call_ct hL)).mono
    (fun _ _ h => ⟨h.1,h.2.1,trivial,trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc hd
    exact WP.mono (reduce_step hc hL ha) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩
  · intro s hc hd
    exact WP.mono (reduce_step hc hL hb) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩

theorem extend_ct (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 64=
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro s hc hd
    exact extend_step hc hd
  · intro s hc hd
    exact extend_step hc hd

end VG.Proof.Ed25519.AArch64.VerifyMessage

import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTReady

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def reduceValues : List (Reg × Value) := [(.r0,.frame 120),(.r1,.frame 184),(.r2,.caller 4 0)]

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L reduceValues []))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct reduce_noFrames
  · intro g m t _ hs
    have a0 := hs.1 (.r0,.frame 120) (by simp [reduceValues])
    have a1 := hs.1 (.r1,.frame 184) (by simp [reduceValues])
    have a2 := hs.1 (.r2,.caller 4 0) (by simp [reduceValues])
    change t.gpr .r2=L.scr+0#32 at a2
    exact reduce_ready hL (by decide) ⟨a0,a1,a2.trans (BitVec.add_zero _)⟩
  · intro a b ar aw br bw h
    simp only [scalarReduceLocal,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨two_sp h,call_gpr_eq h (p := (.r0,.frame 120)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.r1,.frame 184)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.r2,.caller 4 0)) (by simp [reduceValues]) (by decide)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64=digest)
      (callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32=Spec.Ed25519.scalarReduce digest) := by
  have hs := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb reduceValues []
    (by decide) (by simp [reduceValues,valid]) (by decide) (by simp)
    (by simp [reduceValues,preserved])
  refine two_wp ((hs.seq (reduce_call_ct hL)).mono
    (fun _ _ h => ⟨h.1,h.2.1,trivial,trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc hd
    exact WP.mono (reduce_step hc hL ha) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩
  · intro s hc hd
    exact WP.mono (reduce_step hc hL hb) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩

theorem extend_ct (hL : L.Ok) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32=Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 64=
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  refine two_wp ((Whole.zeroWords_ct 38 8).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro s hc hd
    exact extend_step hc hL hd
  · intro s hc hd
    exact extend_step hc hL hd

end VG.Proof.Ed25519.Arm.VerifyMessage

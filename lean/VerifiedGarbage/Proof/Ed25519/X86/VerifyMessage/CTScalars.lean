import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.CTHashPipeline

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.frame 128, .frame 192, .caller 4 0]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarReduce_ok scalarReduce_ct Whole.reduce_nosp (by rw [Whole.reduce_stack]; decide)
  · intro g m t hc hs
    exact reduce_ready hc hL (hs.slot hL (j := 0) (by decide) (by decide))
      (hs.slot hL (j := 1) (by decide) (by decide))
      ((hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 3),
      call_args_eq hL (by decide) h (by decide : 1 < 3), call_args_eq hL (by decide) h (by decide : 2 < 3)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = digest)
      (VG.Impl.Ed25519.X86.PublicKey.callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest) := by
  have ct := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 128, .frame 192, .caller 4 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (reduce_call_ct hL)
  refine two_wp (ct.mono (fun _ _ h => ⟨h.1, h.2.1, trivial, trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc hd
    refine WP.mono (reduce_step hc hL ha) fun _ ⟨hu, hr⟩ => ⟨hu, ?_⟩
    rw [hd] at hr
    exact hr
  · intro t hc hd
    refine WP.mono (reduce_step hc hL hb) fun _ ⟨hu, hr⟩ => ⟨hu, ?_⟩
    rw [hd] at hr
    exact hr

theorem extend_ct (hL : L.Ok) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  exact two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide))
    (fun _ hc hd => extend_step hc hL hd) (fun _ hc hd => extend_step hc hL hd)

end VG.Proof.Ed25519.X86.VerifyMessage

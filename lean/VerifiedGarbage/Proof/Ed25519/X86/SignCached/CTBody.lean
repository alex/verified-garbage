import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTPrimitives
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTHashPipeline

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have r96 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 96, .frame 192, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (reduce_call_ct hL 96 (by decide) (by decide))
  have r128 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 128, .frame 192, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (reduce_call_ct hL 128 (by decide) (by decide))
  have b := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 0, .frame 96, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (base_call_ct hL)
  have m := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (mul_call_ct hL)
  exact ((hashSeed_ct hL ha hb).seq (saveSecret_ct hL)).seq
    (((hashNonce_ct hL ha hb).seq (r96.seq b)).seq
      (((hashChallenge_ct hL ha hb).seq (r128.seq m)).seq (wipe_ct hL)))

end VG.Proof.Ed25519.X86.SignCached

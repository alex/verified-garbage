import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTHashPipeline
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTPrimitives
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTBlocks

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 184) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (reduce d)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 256; omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ [] (by simp) hvall (by decide) (by simp) (by simp [preserved])).seq
    (reduce_call_ct hL d hd)

theorem base_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] []
    (by decide) (by simp [Whole.valid]) (by decide) (by simp [Whole.valid]) (by simp [preserved])).seq
    (base_call_ct hL)

theorem mul_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.Arm.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120),
    (.r3, .frame 24)] [.caller 5 0]
    (by decide) (by simp [Whole.valid]) (by decide) (by simp [Whole.valid]) (by simp [preserved])).seq
    (mul_call_ct hL)

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  ((hashSeed_ct hL ha hb).seq (saveSecret_ct hL)).seq
    (((hashNonce_ct hL ha hb).seq ((reduce_ct hL ha hb 88 (by decide)).seq
      (base_ct hL ha hb))).seq
      (((hashChallenge_ct hL ha hb).seq ((reduce_ct hL ha hb 120 (by decide)).seq
        (mul_ct hL ha hb))).seq (wipe_ct hL)))

end VG.Proof.Ed25519.Arm.SignCached

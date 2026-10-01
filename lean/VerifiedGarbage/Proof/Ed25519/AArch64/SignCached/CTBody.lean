import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTHashPipeline
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTPrimitives

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 256)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (reduceArgs d)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (reduce d)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 4096; omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (reduce_call_ct hL d hd)

theorem base_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]
    (by decide) (by simp [Whole.valid]) (by simp [preserved]) (by taint_decide)).seq
    (base_call_ct hL)

theorem mul_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128),
    (.x3, .frame 32), (.x4, .caller 5 0)]
    (by decide) (by simp [Whole.valid]) (by simp [preserved]) (by taint_decide)).seq
    (mul_call_ct hL)

theorem body_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  ((hashSeed_ct backend hL ha hb).seq saveSecret_ct).seq
    (((hashNonce_ct backend hL ha hb).seq ((reduce_ct hL ha hb 96 (by decide) (by taint_decide)).seq
      (base_ct hL ha hb))).seq
      (((hashChallenge_ct backend hL ha hb).seq ((reduce_ct hL ha hb 128 (by decide) (by taint_decide)).seq
        (mul_ct hL ha hb))).seq (wipe_ct hL)))

end VG.Proof.Ed25519.AArch64.SignCached

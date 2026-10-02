import VerifiedGarbage.Proof.Blake2.Arm.Stream.CT
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Init
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Implies
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming BLAKE2 on ARMv7: `Verified`

The streaming functions are `Verified` against any contract their ARMv7
contracts (`initArm`, `updateArm`, `finalizeArm`) imply, for any parameter set
`P` with `Ok P` and, for `update` and `finalize`, any compression function
verified against `compressArm P` (`CalleeOk`). `init`'s code holds the initial
hash value as immediates, so its taint check is made for each parameter set:
`init_check_s` and `init_check_b`. The implications of the shared contracts
are in `Implies.lean` (`updateS_implies`, …).
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (update finalize)
open VG.Proof.Blake2 (initArm updateArm finalizeArm)

theorem okS : Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩
theorem okB : Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩

variable {w : Nat} {P : Params w}

theorem update_verified (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    {k : Contract isa} (hk : (updateArm P).Implies k) :
    Verified Arm.target (update (w := w) name code) k :=
  Verified.of_correct (fun _ hs => Update.correct hP hf (Update.pre_of hs)) (Update.update_ct hP hf) hk

theorem finalize_verified (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    {k : Contract isa} (hk : (finalizeArm P).Implies k) :
    Verified Arm.target (finalize (w := w) name code) k :=
  Verified.of_correct (fun _ hs => Finalize.correct hP hf (Finalize.pre_of hs)) (Finalize.finalize_ct hP hf) hk

/-- `init`'s taint check, from its arguments. -/
def InitCheck (P : Params w) : Prop :=
  ∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3])
    (Impl.Blake2.Arm.Stream.init P) hc).isSome = true

theorem init_check_s : InitCheck Spec.Blake2.s := ⟨_, by taint_decide⟩
theorem init_check_b : InitCheck Spec.Blake2.b := ⟨_, by taint_decide⟩

theorem init_verified (hP : Ok P) (hc : InitCheck P) {k : Contract isa} (hk : (initArm P).Implies k) :
    Verified Arm.target (Impl.Blake2.Arm.Stream.init P) k := by
  obtain ⟨_, hc⟩ := hc
  refine Verified.of_correct (fun _ hs => Init.correct hP hs) ?_ hk
  refine VG.Taint.constantTime (A := taint) (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s₁ s₂ _ _ ⟨h0, h1, h2, h3⟩ => VG.Arm.Taint.agree_ofRegs fun r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

end VG.Proof.Blake2.Arm.Stream

import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top

/-!
# ML-DSA verification on x86 (32-bit): the contract

`vg_mldsa*_verify` of the parameter sets of Table 1 meets `verifyContract`
with 96 bytes of stack (`verify_verified`), for any verified implementations
of the primitives it calls (`PrimsOk`): the body, as a leaf (`topLeaf`), from
the contract's precondition and public data (`pre_of`, `pub_of`), to its
postcondition (`VFin`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params)

/-- Memory with the arguments `0`, `0x1000`, `0x3000` and `0x10000` at `0x5004`. -/
def satMemV : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500d then 0x30 else if a = 0x5012 then 1 else 0

/-- A state satisfying the precondition. -/
def verifySat (p : Params) : State :=
  satState satMemV [⟨0, p.pkLen⟩, ⟨0x1000, 64⟩, ⟨0x3000, p.sigLen⟩] [⟨0x10000, scrLenV p⟩, ⟨0x5004, 16⟩]

theorem verify_verified {P : Prims} (hP : PrimsOk P) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified X86.target (verify P p) (Spec.MlDsa.verifyContract p X86.abi 96) := by
  have hF := vfacts hp
  refine Piece.verified (((topLeaf (body_nosp hP p) ((body_piece hP hF).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨h.1.1, h⟩)).pre_mono (fun _ h => pre_of h)
    fun _ _ _ _ h => pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, ⟨⟨-, hd⟩, hax⟩, hm, hax'⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [sw_app, hax', hax]
    simp only [vPk, vMu, vSig, addr0] at hd
    exact hd
  · rcases hp with rfl | rfl | rfl
    · exact ⟨verifySat Spec.MlDsa.mlDsa44, by sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, verifySat, satState, satMemV]⟩
    · exact ⟨verifySat Spec.MlDsa.mlDsa65, by sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, verifySat, satState, satMemV]⟩
    · exact ⟨verifySat Spec.MlDsa.mlDsa87, by sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, verifySat, satState, satMemV]⟩

end VG.Proof.MlDsa.X86.Verify

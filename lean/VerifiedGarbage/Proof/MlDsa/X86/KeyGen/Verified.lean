import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Top

/-!
# ML-DSA key generation on x86 (32-bit): the contract

`vg_mldsa*_keygen` of the parameter sets of Table 1 meets `keyGenContract`
with 96 bytes of stack (`keyGen_verified`), for any verified implementations
of the primitives it calls (`PrimsOk`): the body, as a leaf (`topLeaf`), from
the contract's precondition and public data (`pre_of`, `pub_of`), to its
postcondition (`post`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params)

/-- Memory with the arguments `0`, `0x1000`, `0x3000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500d then 0x30 else if a = 0x5012 then 1 else 0

/-- A state satisfying the precondition. -/
def keyGenSat (p : Params) : State :=
  satState satMem [⟨0, 32⟩] [⟨0x1000, p.pkLen⟩, ⟨0x3000, p.skLen⟩, ⟨0x10000, scrLen p⟩, ⟨0x5004, 16⟩]

theorem keyGen_verified {P : Prims} (hP : PrimsOk P) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified X86.target (keyGen P p) (Spec.MlDsa.keyGenContract p X86.abi 96) := by
  have hF := pfacts hp
  refine Piece.verified (((topLeaf (body_nosp hP p) (body_piece hP hF)).pre_mono (fun _ h => pre_of h)
    fun _ _ _ _ h => pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [sw_app, hax, hd.eax, hm]
    have r := post hF (pre_of h₀) hd
    simp only [xiOf, addr0] at r
    exact r
  · rcases hp with rfl | rfl | rfl
    · exact ⟨keyGenSat Spec.MlDsa.mlDsa44, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, keyGenSat, satState, satMem]⟩
    · exact ⟨keyGenSat Spec.MlDsa.mlDsa65, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, keyGenSat, satState, satMem]⟩
    · exact ⟨keyGenSat Spec.MlDsa.mlDsa87, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, keyGenSat, satState, satMem]⟩

end VG.Proof.MlDsa.X86.KeyGen
